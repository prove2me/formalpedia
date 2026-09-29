-- Prove2me | solution 1 for HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e024abab-e812-510d-bbb1-6f2ad6ced014

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul

set_option autoImplicit false

namespace ATHRDeriv

open MvPolynomial HeckeEis Finset

section Monomials

variable (K : Type*) [Field K]

noncomputable def e (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[scoped simp] theorem e_zero (i j : ℕ) : e i j 0 = i := by simp [e]

@[scoped simp] theorem e_one (i j : ℕ) : e i j 1 = j := by simp [e]

theorem e_eq_iff {i j i' j' : ℕ} : e i j = e i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
      by simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem eq_e (d : Fin 2 →₀ ℕ) : d = e (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp

theorem degree_e (i j : ℕ) : Finsupp.degree (e i j) = i + j := by
  rw [e, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem monomial_e (i j : ℕ) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) = C c * X 0 ^ i * X 1 ^ j := by
  rw [e, mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, C_mul_monomial, one_mul, mul_one]

theorem isHomogeneous_monomial_e (i j : ℕ) (c : K) :
    ((monomial (e i j) c : MvPolynomial (Fin 2) K)).IsHomogeneous (i + j) :=
  isHomogeneous_monomial _ (degree_e i j)

theorem monomial_e_mem {i j n : ℕ} (h : i + j = n) (c : K) :
    (monomial (e i j) c : MvPolynomial (Fin 2) K) ∈ BinaryForm K n := by
  rw [MvPolynomial.mem_homogeneousSubmodule, ← h]
  exact isHomogeneous_monomial_e K i j c

theorem deg_two {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) {d : Fin 2 →₀ ℕ}
    (hd : coeff d F ≠ 0) : d 0 + d 1 = n := by
  have hdeg := hF hd
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at hdeg
  simpa only [Pi.one_apply, smul_eq_mul, mul_one, Fin.sum_univ_two] using hdeg

theorem isHomogeneous_coe {n : ℕ} (F : ↥(BinaryForm K n)) :
    (F : MvPolynomial (Fin 2) K).IsHomogeneous n :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mp F.2

theorem eq_sum_monomial {F : MvPolynomial (Fin 2) K} {n : ℕ} (hF : F.IsHomogeneous n) :
    F = ∑ i ∈ range (n + 1), monomial (e i (n - i)) (coeff (e i (n - i)) F) := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : coeff d F = 0
  · rw [hd]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · rw [← h] at hd
      exact hd
    · rfl
  · have hdeg := deg_two K hF hd
    rw [Finset.sum_eq_single (d 0)]
    · have h : e (d 0) (n - d 0) = d := by
        conv_rhs => rw [eq_e d]
        rw [e_eq_iff]
        exact ⟨rfl, by omega⟩
      rw [if_pos h, h]
    · intro i _ hne
      rw [if_neg]
      intro h
      apply hne
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
      simpa using this
    · intro h
      exfalso
      simp only [mem_range] at h
      omega

end Monomials

section Remap

variable (K : Type*) [Field K]

noncomputable def remap (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) :
    MvPolynomial (Fin 2) K →ₗ[K] MvPolynomial (Fin 2) K :=
  ∑ i ∈ S, (lcoeff K (e i (n - i))).smulRight (monomial (e (g i) (h i)) (w i))

theorem remap_apply (S : Finset ℕ) (n : ℕ) (w : ℕ → K) (g h : ℕ → ℕ) (F : MvPolynomial (Fin 2) K) :
    remap K S n w g h F = ∑ i ∈ S, monomial (e (g i) (h i)) (coeff (e i (n - i)) F * w i) := by
  rw [remap, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smulRight_apply, lcoeff_apply, smul_monomial, smul_eq_mul]

theorem remap_mem {S : Finset ℕ} {n : ℕ} {w : ℕ → K} {g h : ℕ → ℕ} {m : ℕ}
    (hgh : ∀ i ∈ S, g i + h i = m) (F : MvPolynomial (Fin 2) K) :
    remap K S n w g h F ∈ BinaryForm K m := by
  rw [remap_apply]
  exact Submodule.sum_mem _ fun i hi => monomial_e_mem K (hgh i hi) _

end Remap

section Dmap

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

noncomputable def D (i : Fin 2) : Module.End K (MvPolynomial (Fin 2) K) :=
  (pderiv i : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K)).toLinearMap

theorem D_apply (i : Fin 2) (F : MvPolynomial (Fin 2) K) : D K i F = pderiv i F := rfl

theorem pderiv_comm (i j : Fin 2) (F : MvPolynomial (Fin 2) K) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f k hf =>
    have h0 : ∀ i' j' : Fin 2, pderiv i' ((Pi.single j' 1 : Fin 2 → MvPolynomial (Fin 2) K) k) = 0 := by
      intro i' j'
      by_cases hjk : k = j'
      · subst hjk
        simp
      · rw [Pi.single_eq_of_ne hjk, map_zero]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, h0, mul_zero, hf]
    ring

theorem commute_D : Commute (D K 0) (D K 1) := by
  change D K 0 * D K 1 = D K 1 * D K 0
  refine LinearMap.ext fun F => ?_
  simp only [Module.End.mul_apply, D_apply]
  exact pderiv_comm K 0 1 F

theorem isHomogeneous_D_pow (i : Fin 2) (t : ℕ) {F : MvPolynomial (Fin 2) K} {n : ℕ}
    (hF : F.IsHomogeneous n) : ((D K i ^ t) F).IsHomogeneous (n - t) := by
  induction t with
  | zero => simpa using hF
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, D_apply]
    have := ih.pderiv (i := i)
    rwa [Nat.sub_sub] at this

theorem D_zero_pow_monomial (t : ℕ) (s : Fin 2 →₀ ℕ) (c : K) :
    (D K 0 ^ t) (monomial s c) = monomial (s - Finsupp.single 0 t) (c * ((s 0).descFactorial t : ℕ)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, D_apply, pderiv_monomial, Nat.descFactorial_succ]
    have hs : s - Finsupp.single 0 t - Finsupp.single 0 1 = s - Finsupp.single (0 : Fin 2) (t + 1) := by
      ext k
      fin_cases k <;> simp
      omega
    have hc : c * ((s 0).descFactorial t : ℕ) * (((s - Finsupp.single 0 t : Fin 2 →₀ ℕ) 0 : ℕ) : K)
        = c * (((s 0 - t) * (s 0).descFactorial t : ℕ) : K) := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
      push_cast
      ring
    rw [hs, hc]

theorem euler_p {H : MvPolynomial (Fin 2) K} (hH : H.IsHomogeneous p) :
    X 0 * pderiv 0 H + X 1 * pderiv 1 H = 0 := by
  have h := hH.sum_X_mul_pderiv
  rw [Fin.sum_univ_two] at h
  rw [h, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

noncomputable def dmap (a : ℕ) : MvPolynomial (Fin 2) K →ₗ[K] MvPolynomial (Fin 2) K :=
  remap K (Ico a p) (a + (p - 1)) (fun i => (i.descFactorial a : K)) (fun i => i - a) (fun i => p - 1 - i)

theorem dmap_mem (a : ℕ) (F : MvPolynomial (Fin 2) K) : dmap p K a F ∈ BinaryForm K (p - 1 - a) :=
  remap_mem K (fun i hi => by simp only [mem_Ico] at hi; omega) F

theorem cast_descFactorial_eq_zero {a i : ℕ} (hpi : p ≤ i) (hi : i < p + a) :
    ((i.descFactorial a : ℕ) : K) = 0 := by
  apply (CharP.cast_eq_zero_iff K p _).mpr
  rw [Nat.descFactorial_eq_prod_range]
  have hmem : i - p ∈ range a := by simp; omega
  have h := Finset.dvd_prod_of_mem (fun t => i - t) hmem
  rwa [show i - (i - p) = p by omega] at h

theorem D_zero_pow_eq {a : ℕ} {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous (a + (p - 1))) :
    (D K 0 ^ a) F = X 1 ^ a * dmap p K a F := by
  set N := a + (p - 1) with hN
  conv_lhs => rw [eq_sum_monomial K hF]
  rw [map_sum, dmap, remap_apply, Finset.mul_sum]
  simp only [D_zero_pow_monomial, e_zero]
  have hsub : Ico a p ⊆ range (N + 1) := by
    intro i hi
    simp only [mem_Ico, mem_range] at hi ⊢
    omega
  have hvan : ∀ i ∈ range (N + 1), i ∉ Ico a p →
      (monomial (e i (N - i) - Finsupp.single 0 a) (coeff (e i (N - i)) F * ((i.descFactorial a : ℕ) : K))
        : MvPolynomial (Fin 2) K) = 0 := by
    intro i hi hi'
    simp only [mem_range, mem_Ico, not_and, not_lt] at hi hi'
    have : ((i.descFactorial a : ℕ) : K) = 0 := by
      rcases Nat.lt_or_ge i a with h | h
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero]
      · have hp1 := hp.out.one_le
        exact cast_descFactorial_eq_zero p K (hi' h) (by omega)
    rw [this, mul_zero, map_zero]
  rw [← Finset.sum_subset hsub hvan]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [mem_Ico] at hi
  have hs : e i (N - i) - Finsupp.single 0 a = Finsupp.single (1 : Fin 2) a + e (i - a) (p - 1 - i) := by
    ext k
    fin_cases k <;> simp [e] <;> omega
  rw [X_pow_eq_monomial, monomial_mul, one_mul, hs]

theorem D_pow_D_pow_eq {a : ℕ} {F : MvPolynomial (Fin 2) K} (hF : F.IsHomogeneous (a + (p - 1)))
    {k : ℕ} (hk : k ≤ a) :
    (D K 0 ^ (a - k)) ((D K 1 ^ k) F) = (-1) ^ k * X 0 ^ k * X 1 ^ (a - k) * dmap p K a F := by
  induction k with
  | zero => simpa using D_zero_pow_eq p K hF
  | succ k ih =>
    have ih' := ih (by omega)
    have hp1 := hp.out.one_le
    set H := (D K 0 ^ (a - (k + 1))) ((D K 1 ^ k) F) with hH
    have hHhom : H.IsHomogeneous p := by
      have h2 := isHomogeneous_D_pow K 0 (a - (k + 1)) (isHomogeneous_D_pow K 1 k hF)
      have : a + (p - 1) - k - (a - (k + 1)) = p := by omega
      rwa [this] at h2
    have heuler := euler_p p K hHhom
    have hD0H : pderiv 0 H = (D K 0 ^ (a - k)) ((D K 1 ^ k) F) := by
      rw [hH, ← D_apply K 0, ← Module.End.mul_apply, ← pow_succ', show a - (k + 1) + 1 = a - k by omega]
    have hD1H : pderiv 1 H = (D K 0 ^ (a - (k + 1))) ((D K 1 ^ (k + 1)) F) := by
      calc pderiv 1 H = (D K 1 * D K 0 ^ (a - (k + 1))) ((D K 1 ^ k) F) := by
            rw [Module.End.mul_apply, hH, D_apply]
        _ = (D K 0 ^ (a - (k + 1)) * D K 1) ((D K 1 ^ k) F) := by
            rw [((commute_D K).symm.pow_right (a - (k + 1))).eq]
        _ = (D K 0 ^ (a - (k + 1))) ((D K 1 ^ (k + 1)) F) := by
            rw [Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    refine mul_left_cancel₀ (X_ne_zero (1 : Fin 2)) ?_
    rw [← hD1H, show X 1 * pderiv 1 H = -(X 0 * pderiv 0 H) by linear_combination heuler, hD0H, ih']
    have hx : (X 1 : MvPolynomial (Fin 2) K) ^ (a - k) = X 1 * X 1 ^ (a - (k + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hx]
    ring

theorem pderiv_zero_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (F : MvPolynomial (Fin 2) K) :
    pderiv 0 (binarySubst K M F) =
      C ((M 0 0 : ℤ) : K) * binarySubst K M (pderiv 0 F) +
        C ((M 0 1 : ℤ) : K) * binarySubst K M (pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg]
    ring
  | mul_X f j hf =>
    rw [map_mul, pderiv_mul, hf, binarySubst_X]
    fin_cases j <;> simp [binarySubst_X, Fin.sum_univ_two] <;> ring

noncomputable def Zop (M : Matrix (Fin 2) (Fin 2) ℤ) : Module.End K (MvPolynomial (Fin 2) K) :=
  ((M 0 0 : ℤ) : K) • D K 0 + ((M 0 1 : ℤ) : K) • D K 1

theorem Zop_apply (M : Matrix (Fin 2) (Fin 2) ℤ) (G : MvPolynomial (Fin 2) K) :
    Zop K M G = C ((M 0 0 : ℤ) : K) * pderiv 0 G + C ((M 0 1 : ℤ) : K) * pderiv 1 G := by
  rw [Zop, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, D_apply, D_apply,
    smul_eq_C_mul, smul_eq_C_mul]

theorem D_zero_pow_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (t : ℕ) (F : MvPolynomial (Fin 2) K) :
    (D K 0 ^ t) (binarySubst K M F) = binarySubst K M ((Zop K M ^ t) F) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, D_apply, pderiv_zero_binarySubst, pow_succ',
      Module.End.mul_apply, Zop_apply, map_add, map_mul, map_mul, binarySubst_C, binarySubst_C]

theorem Zop_pow_apply (M : Matrix (Fin 2) (Fin 2) ℤ) (a : ℕ) (F : MvPolynomial (Fin 2) K) :
    (Zop K M ^ a) F = ∑ k ∈ range (a + 1),
      (((M 0 0 : ℤ) : K) ^ k * ((M 0 1 : ℤ) : K) ^ (a - k) * (a.choose k : ℕ)) •
        (D K 0 ^ k) ((D K 1 ^ (a - k)) F) := by
  have hc : Commute (((M 0 0 : ℤ) : K) • D K 0) (((M 0 1 : ℤ) : K) • D K 1) :=
    ((commute_D K).smul_left _).smul_right _
  rw [Zop, hc.add_pow, LinearMap.sum_apply]
  refine sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, smul_pow, smul_pow,
    LinearMap.smul_apply, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul K]
  simp only [map_smul, smul_smul]
  congr 1
  ring

theorem dmap_binarySubst {a : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) {F : MvPolynomial (Fin 2) K}
    (hF : F.IsHomogeneous (a + (p - 1))) :
    dmap p K a (binarySubst K M F) = (((M.det : ℤ) : K) ^ a) • binarySubst K M (dmap p K a F) := by
  have hMF : (binarySubst K M F).IsHomogeneous (a + (p - 1)) :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp
      (binarySubst_mem K M ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr hF))
  have h1 := D_zero_pow_eq p K hMF
  set u : MvPolynomial (Fin 2) K := binarySubst K M (X 0) with hu
  set w : MvPolynomial (Fin 2) K := binarySubst K M (X 1) with hw
  have h2 : (D K 0 ^ a) (binarySubst K M F)
      = (C ((M 0 0 : ℤ) : K) * w + -(C ((M 0 1 : ℤ) : K) * u)) ^ a * binarySubst K M (dmap p K a F) := by
    rw [D_zero_pow_binarySubst, Zop_pow_apply, map_sum, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hka : k ≤ a := by simpa [Nat.lt_succ_iff] using hk
    have hG := D_pow_D_pow_eq p K hF (k := a - k) (by omega)
    rw [Nat.sub_sub_self hka] at hG
    rw [map_smul, hG]
    simp only [map_mul, map_pow, map_neg, map_one, smul_eq_C_mul, map_natCast]
    rw [← hu, ← hw]
    ring
  have hlin : C ((M 0 0 : ℤ) : K) * w + -(C ((M 0 1 : ℤ) : K) * u)
      = C ((M.det : ℤ) : K) * X 1 := by
    rw [hu, hw, binarySubst_X, binarySubst_X, Matrix.det_fin_two]
    simp only [Fin.sum_univ_two, Int.cast_sub, Int.cast_mul, map_sub, map_mul]
    ring
  have h3 : (X 1 : MvPolynomial (Fin 2) K) ^ a * dmap p K a (binarySubst K M F)
      = X 1 ^ a * ((((M.det : ℤ) : K) ^ a) • binarySubst K M (dmap p K a F)) := by
    rw [← h1, h2, hlin, mul_pow, smul_eq_C_mul, map_pow]
    ring
  exact mul_left_cancel₀ (pow_ne_zero a (X_ne_zero (1 : Fin 2))) h3

noncomputable def Dlin (a : ℕ) : ↥(BinaryForm K (a + (p - 1))) →ₗ[K] ↥(BinaryForm K (p - 1 - a)) :=
  LinearMap.codRestrict (BinaryForm K (p - 1 - a)) ((dmap p K a).comp (BinaryForm K _).subtype)
    fun F => dmap_mem p K a _

@[scoped simp] theorem coe_Dlin (a : ℕ) (F : ↥(BinaryForm K (a + (p - 1)))) :
    ((Dlin p K a F : ↥(BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K) = dmap p K a F :=
  rfl

theorem Dlin_equivar (a : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(BinaryForm K (a + (p - 1)))) :
    Dlin p K a (binaryFormRep K _ M F) = (((M.det : ℤ) : K) ^ a) • binaryFormRep K _ M (Dlin p K a F) := by
  refine Subtype.ext ?_
  simp only [coe_Dlin, binaryFormRep_apply_coe, Submodule.coe_smul]
  exact dmap_binarySubst p K M (isHomogeneous_coe K F)

end Dmap

end ATHRDeriv
p2m_reactivate "P2MW.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul.ATHRDeriv"

open MvPolynomial in
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (a : ℕ) :
    ∃ D : ↥(HeckeEis.BinaryForm K (a + (p - 1))) →ₗ[K] ↥(HeckeEis.BinaryForm K (p - 1 - a)),
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = ∑ k ∈ Finset.Ico a p,
              monomial (Finsupp.single 0 (k - a) + Finsupp.single 1 (p - 1 - k))
                (coeff (Finsupp.single 0 k + Finsupp.single 1 (a + (p - 1) - k))
                  (F : MvPolynomial (Fin 2) K) * (k.descFactorial a : K))) ∧
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        (X 1 : MvPolynomial (Fin 2) K) ^ a
            * ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = (fun G : MvPolynomial (Fin 2) K => pderiv 0 G)^[a] (F : MvPolynomial (Fin 2) K)) ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(HeckeEis.BinaryForm K (a + (p - 1)))),
        D (HeckeEis.binaryFormRep K (a + (p - 1)) M F)
          = (((M.det : ℤ) : K) ^ a) • HeckeEis.binaryFormRep K (p - 1 - a) M (D F)) := by
  refine ⟨ATHRDeriv.Dlin p K a, fun F => ?_, fun F => ?_, fun M F => ATHRDeriv.Dlin_equivar p K a M F⟩
  · rw [ATHRDeriv.coe_Dlin, ATHRDeriv.dmap, ATHRDeriv.remap_apply]
    rfl
  · rw [ATHRDeriv.coe_Dlin, ← ATHRDeriv.D_zero_pow_eq p K (ATHRDeriv.isHomogeneous_coe K F),
      Module.End.pow_apply]
    rfl

end S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul
end P2MW
export P2MW.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul (solution)
