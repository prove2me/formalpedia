-- Prove2me | solution 1 for HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/89891b28-dbae-5deb-a133-937e9bb4ca9b

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_Gamma0NebenRep
import Theorems.Thm_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
import Theorems.Thm_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd
import Theorems.Thm_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL

set_option autoImplicit false

namespace WeightTwoAssembly

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section OddVanishing

variable (κ : Type) [Field κ]

theorem binarySubst_neg_one_of_mem {n : ℕ} {F : MvPolynomial (Fin 2) κ} (hF : F ∈ BinaryForm κ n) :
    binarySubst κ (-1 : Matrix (Fin 2) (Fin 2) ℤ) F = ((-1 : κ) ^ n) • F := by
  classical
  have hX : ∀ j : Fin 2,
      (∑ i : Fin 2, MvPolynomial.C ((((-1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : κ)) * MvPolynomial.X i :
        MvPolynomial (Fin 2) κ) = -MvPolynomial.X j := by
    intro j
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp
  have hsubst : binarySubst κ (-1 : Matrix (Fin 2) (Fin 2) ℤ) =
      MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) κ)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [binarySubst_X, MvPolynomial.aeval_X, hX]
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF
  rw [hsubst]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have hprod : (d.prod fun i k => (-(MvPolynomial.X i : MvPolynomial (Fin 2) κ)) ^ k) =
      (d.prod fun _ k => ((-1 : MvPolynomial (Fin 2) κ)) ^ k) * d.prod fun i k => MvPolynomial.X i ^ k := by
    rw [← Finsupp.prod_mul]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [← mul_pow, neg_one_mul]
  have hsign : (d.prod fun _ k => ((-1 : MvPolynomial (Fin 2) κ)) ^ k) = (-1 : MvPolynomial (Fin 2) κ) ^ n := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
  rw [hprod, hsign, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

variable (N n : ℕ)

noncomputable abbrev ρSym : Representation κ (Gamma0 N) ↥(BinaryForm κ n) :=
  (binaryFormRepSL κ n).comp (Gamma0 N).subtype

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  simp

def negOne : Gamma0 N := ⟨-1, neg_one_mem_Gamma0 N⟩

theorem negOne_mul_comm (g : Gamma0 N) : g * negOne N = negOne N * g := by
  apply Subtype.ext
  change (g : SL(2, ℤ)) * (-1) = (-1) * (g : SL(2, ℤ))
  rw [mul_neg_one, neg_one_mul]

theorem ρSym_negOne (v : ↥(BinaryForm κ n)) : ρSym κ N n (negOne N) v = ((-1 : κ) ^ n) • v := by
  apply Subtype.ext
  change binarySubst κ (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (v : MvPolynomial (Fin 2) κ) =
    (((-1 : κ) ^ n) • v : ↥(BinaryForm κ n))
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Submodule.coe_smul]
  exact binarySubst_neg_one_of_mem κ v.2

theorem coeffH1_eq_zero_of_odd (h2 : (2 : κ) ≠ 0) (hn : Odd n) (x : coeffH1 (ρSym κ N n)) : x = 0 := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  rw [coeffH1Mk_eq_zero_iff]
  have hneg : ∀ w : ↥(BinaryForm κ n), ρSym κ N n (negOne N) w = -w := fun w => by
    rw [ρSym_negOne, hn.neg_one_pow, neg_one_smul κ w]
  have hz := z.2
  have key : ∀ g : Gamma0 N,
      (2 : κ) • (z : Gamma0 N → ↥(BinaryForm κ n)) g =
        (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N) -
          ρSym κ N n g ((z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)) := by
    intro g
    have h1 := hz g (negOne N)
    have h2' := hz (negOne N) g
    rw [← negOne_mul_comm N g, h1, hneg] at h2'
    have e1 : (z : Gamma0 N → ↥(BinaryForm κ n)) g +
        ρSym κ N n g ((z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)) +
        (z : Gamma0 N → ↥(BinaryForm κ n)) g = (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N) := by
      rw [h2']
      abel
    rw [two_smul, eq_sub_iff_add_eq]
    convert e1 using 1
    abel
  refine (mem_coeffCoboundaries_iff _ _).mpr
    ⟨-((2 : κ)⁻¹ • (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)), funext fun g => ?_⟩
  have hhalf : (2 : κ)⁻¹ • ((2 : κ) • (z : Gamma0 N → ↥(BinaryForm κ n)) g) =
      (z : Gamma0 N → ↥(BinaryForm κ n)) g := by
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [map_neg, map_smul, neg_sub_neg]
  conv_rhs => rw [← hhalf, key g, smul_sub]

end OddVanishing

theorem natCast_pow_sub_one_eq_one (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : (ℓ : F) ^ (p - 1) = 1 := by
  have hne : (ℓ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have h := ZMod.pow_card_sub_one_eq_one hne
  have := congrArg (ZMod.castHom (dvd_refl p) F) h
  rwa [map_pow, map_natCast, map_one] at this

theorem isEigensystemH1_mono {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V] {M : ℕ}
    (ρ : Representation K (Gamma0 M) V) (a : ℕ → (V →ₗ[K] V)) {S S' : Set ℕ} (hSS' : S ⊆ S') (lam : ℕ → K)
    (h : IsEigensystemH1 M ρ a S lam) : IsEigensystemH1 M ρ a S' lam := by
  obtain ⟨x, hx, heig⟩ := h
  exact ⟨x, hx, fun ℓ hℓ hℓM hℓS => heig ℓ hℓ hℓM (fun h => hℓS (hSS' h))⟩

end WeightTwoAssembly

open scoped MatrixGroups in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ (M : ℕ) (mu : ℕ → κ), M ∣ N * p ^ 2 ∧
      HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ (n / 2) * mu ℓ := by
  classical
  have hp : p.Prime := Fact.out

  have hpar : Even n ∨ p = 2 := by
    by_cases hp2 : p = 2
    · exact Or.inr hp2
    · left
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      have h2 : (2 : κ) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : κ) = 0 := by exact_mod_cast h
        rw [CharP.cast_eq_zero_iff κ p] at h'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      obtain ⟨x, hx, -⟩ := hocc
      exact hx (WeightTwoAssembly.coeffH1_eq_zero_of_odd κ N n h2 hodd x)

  obtain ⟨M, hpM, hM0, hNM, hMNp, j, e, nu, hjn, hmod, hnuocc, hlam⟩ :
      ∃ (M : ℕ) (hpM : p ∣ M), M ≠ 0 ∧ N ∣ M ∧ M ∣ N * p ∧ ∃ (j e : ℕ) (nu : ℕ → κ), j ≤ n ∧
        e + 2 * j ≡ n [MOD (p - 1)] ∧
        HeckeEis.IsEigensystemH1 M (HeckeEis.gamma0NebenRep p M hpM κ e) (fun _ => LinearMap.id)
          (insert p S₀) nu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ j * nu ℓ := by
    by_cases hpN : p ∣ N
    · obtain ⟨j, e, nu, hjn, hmod, hnuocc, hlam⟩ :=
        HeckeEis.exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd
          p N hpN S₀ n κ lam hocc
      exact ⟨N, hpN, NeZero.ne N, dvd_rfl, dvd_mul_right N p, j, e, nu, hjn, hmod,
        WeightTwoAssembly.isEigensystemH1_mono _ _ (Set.subset_insert p S₀) nu hnuocc,
        fun ℓ hℓ hℓN _ hℓS => hlam ℓ hℓ hℓN hℓS⟩
    · have hp1 : ((p + 1 : ℕ) : κ) ≠ 0 := by
        rw [Nat.cast_succ, CharP.cast_eq_zero κ p, zero_add]
        exact one_ne_zero
      have hocc' := HeckeEis.isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1 N p hp hpN κ hp1 S₀ n lam hocc
      haveI : NeZero (N * p) := ⟨mul_ne_zero (NeZero.ne N) hp.ne_zero⟩
      have hpNp : p ∣ N * p := dvd_mul_left p N
      obtain ⟨j, e, nu, hjn, hmod, hnuocc, hlam⟩ :=
        HeckeEis.exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd
          p (N * p) hpNp (insert p S₀) n κ lam hocc'
      refine ⟨N * p, hpNp, mul_ne_zero (NeZero.ne N) hp.ne_zero, dvd_mul_right N p, dvd_rfl, j, e, nu, hjn,
        hmod, hnuocc, fun ℓ hℓ hℓN hℓp hℓS => hlam ℓ hℓ ?_ ?_⟩
      · intro h
        rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h2
        · exact hℓN h1
        · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h2)
      · rw [Set.mem_insert_iff]
        rintro (h | h)
        · exact hℓp h
        · exact hℓS h
  haveI : NeZero M := ⟨hM0⟩

  set t : ℕ := j + (p - 2) * (n / 2) with ht
  have het : (p - 1) ∣ e + 2 * t := by
    rcases hpar with hn | hp2
    · have h2n : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
      have hsum : e + 2 * t = (e + 2 * j) + (p - 2) * n := by
        rw [ht, mul_add, ← mul_assoc, mul_comm 2 (p - 2), mul_assoc, h2n]
        ring

      have h1 : e + 2 * t ≡ n + (p - 2) * n [MOD (p - 1)] := by
        rw [hsum]; exact Nat.ModEq.add_right _ hmod
      have h2 : n + (p - 2) * n = (p - 1) * n := by
        have := hp.two_le
        rw [show p - 1 = (p - 2) + 1 by omega]
        ring
      rw [h2] at h1
      exact (Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))))
    · subst hp2
      simp
  obtain ⟨M', mu, hMM', hM'Mp, hmuocc, hmu⟩ :=
    HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep p M hpM (insert p S₀) e t het κ nu
      hnuocc

  refine ⟨M', mu, ?_, ?_, ?_⟩
  · calc M' ∣ M * p := hM'Mp
      _ ∣ N * p * p := mul_dvd_mul_right hMNp p
      _ = N * p ^ 2 := by ring
  · rwa [Set.insert_eq_of_mem (Set.mem_insert p S₀)] at hmuocc
  · intro ℓ hℓ hℓN hℓp hℓS
    have hℓM : ¬ ℓ ∣ M := by
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).mp (h.trans hMNp) with h1 | h2
      · exact hℓN h1
      · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h2)
    have hℓins : ℓ ∉ insert p S₀ := by
      rw [Set.mem_insert_iff]
      rintro (h | h)
      · exact hℓp h
      · exact hℓS h
    rw [hmu ℓ hℓ hℓM hℓp hℓins, hlam ℓ hℓ hℓN hℓp hℓS, ← mul_assoc, ← pow_add]
    congr 1

    have hexp : n / 2 + t = j + (p - 1) * (n / 2) := by
      have := hp.two_le
      rw [ht, show p - 1 = (p - 2) + 1 by omega]
      ring
    rw [hexp, pow_add, pow_mul, WeightTwoAssembly.natCast_pow_sub_one_eq_one p κ hℓ hℓp, one_pow, mul_one]

end S_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
end P2MW
export P2MW.S_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL (solution)
