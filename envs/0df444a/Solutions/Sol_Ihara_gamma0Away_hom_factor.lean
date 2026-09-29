-- Prove2me | solution 1 for Ihara.gamma0Away_hom_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5ac86b8c-257d-5d9c-a5ea-af6616cdc828

import Definitions.Def_IharaMennickeCarrier
import Theorems.Thm_Ihara_gamma0Fin_hom_factor
import Definitions.Def_IharaGamma0Fin
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Theorems.Thm_Ihara_amalgamToGamma0Away_injective
import Theorems.Thm_Ihara_amalgamToGamma0Away_surjective
import Definitions.Def_IharaAmalgam
import Definitions.Def_IharaAmalgamMap
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Theorems.Thm_Ihara_mennickeCSP_of_coprime_of_stem
import Theorems.Thm_Ihara_pow_card_mem_mennickeQ_mul
import Definitions.Def_SchurMultiplierTrivial
import Theorems.Thm_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
import Theorems.Thm_Ihara_prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow
import Theorems.Thm_Ihara_ihxw14_dio_lemma22_statement_unconditional
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_Ihara_principalCongruenceAway_le_commutator_sup_mennickeQ
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
import Theorems.Thm_Ihara_isPerfect_SL2_ZMod_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_gamma0Away_hom_factor

set_option Elab.async false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open scoped MatrixGroups

private theorem two_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 2 ∣ q) : 2 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
  refine ⟨2 * (k * k) + 2 * k, ?_⟩
  have hq2 : q ^ 2 = 2 * (2 * (k * k) + 2 * k) + 1 := by rw [hk]; ring
  rw [hq2, Nat.add_sub_cancel]

private theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (hq : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 := ⟨q / 3, by omega⟩
  rcases hk with h | h
  · refine ⟨3 * (k * k) + 2 * k, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 2 * k) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]
  · refine ⟨3 * (k * k) + 4 * k + 1, ?_⟩
    have hq2 : q ^ 2 = 3 * (3 * (k * k) + 4 * k + 1) + 1 := by rw [h]; ring
    rw [hq2, Nat.add_sub_cancel]

theorem three_lt_of_prime_dvd_of_coprime (q m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m')
    (hm'q : Nat.Coprime m' q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 3 < p := by
  have hnotq : ¬ p ∣ q := by
    intro h
    have hgcd : Nat.gcd m' q = 1 := hm'q
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  have hnotn : ¬ p ∣ q ^ 2 - 1 := by
    intro h
    have hgcd : Nat.gcd m' (q ^ 2 - 1) = 1 := hm'n
    have hp1 : p ∣ 1 := hgcd ▸ Nat.dvd_gcd hpm h
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
  by_contra hle
  rw [not_lt] at hle
  have h23 : p = 2 ∨ p = 3 := by
    have h2 := hp.two_le
    omega
  rcases h23 with rfl | rfl
  · exact hnotn (two_dvd_sq_sub_one_of_not_dvd hnotq)
  · exact hnotn (three_dvd_sq_sub_one_of_not_dvd hnotq)

theorem five_le_of_prime_dvd_block (q m' : ℕ) {p : ℕ} (hp : p.Prime) (hpm : p ∣ m')
    (hm'q : Nat.Coprime m' q) (hm'n : Nat.Coprime m' (q ^ 2 - 1)) : 5 ≤ p := by
  have h3 := three_lt_of_prime_dvd_of_coprime q m' hp hpm hm'q hm'n
  exact hp.five_le_of_ne_two_of_ne_three (by omega) (by omega)

theorem mennickeQ_le_of_dvd (q a b : ℕ) (hdvd : a ∣ b) : mennickeQ q b ≤ mennickeQ q a := by
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff]
  obtain ⟨c, rfl⟩ := hdvd
  rw [pow_mul]
  exact pow_mem (Subgroup.subset_normalClosure (Set.mem_singleton _)) c

section GateSlice

variable (q : ℕ)

theorem qInv_mul_natCast_q_sq :
    qInv q * ((q : ℕ) : ZAway q) ^ 2 = ((q : ℕ) : ZAway q) := by
  rw [pow_two, ← mul_assoc, qInv_mul_natCast_q, one_mul]

theorem slToAway_mennickeA_coe :
    ((slToAway q mennickeA : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; 1, 1] := by
  rw [coe_slToAway, mennickeA_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem slToAway_mennickeA_pow_coe (k : ℕ) :
    (((slToAway q mennickeA) ^ k : SL(2, ZAway q)) :
        Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![1, 0; ((k : ℕ) : ZAway q), 1] := by
  rw [← map_pow, coe_slToAway, mennickeA_pow_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private theorem sl2coeA3_mul {R : Type*} [CommRing R] (A B : SL(2, R)) :
    ((A * B : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) = (A : Matrix (Fin 2) (Fin 2) R) * B := rfl

theorem mennickeU_mul_mennickeA_pow_sq :
    mennickeU q * (slToAway q mennickeA) ^ (q ^ 2) =
      slToAway q mennickeA * mennickeU q := by
  apply Subtype.ext
  rw [sl2coeA3_mul, sl2coeA3_mul,
    slToAway_mennickeA_pow_coe, slToAway_mennickeA_coe, mennickeU_coe,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qInv_mul_natCast_q_sq q]

theorem mennickeU_inv_mul_mennickeA_mul_mennickeU :
    (mennickeU q)⁻¹ * slToAway q mennickeA * mennickeU q =
      (slToAway q mennickeA) ^ (q ^ 2) := by
  rw [mul_assoc, ← mennickeU_mul_mennickeA_pow_sq q, ← mul_assoc, inv_mul_cancel, one_mul]

end GateSlice

end Ihara

section Inl_Thm_IharaA3_MennickeCSPCarrier

end Inl_Thm_IharaA3_MennickeCSPCarrier

section Inl_A3_KillBridge

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Matrix CongruenceSubgroup

open scoped MatrixGroups

section Bridge

variable (N M q : ℕ)

theorem castHom_comp_zAwayToZMod (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q) (hNM : N ∣ M) :
    (ZMod.castHom hNM (ZMod N)).comp (zAwayToZMod M q hMq) = zAwayToZMod N q hNq := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) ?_
  ext a
  simp only [RingHom.comp_apply, zAwayToZMod_algebraMap, map_intCast]

theorem slAwayReduction_mem_Gamma0Fin (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    slAwayReduction M q hMq (g : SL(2, ZAway q)) ∈ Gamma0Fin N M := by
  obtain ⟨r, hr⟩ := g.2
  refine ⟨zAwayToZMod M q hMq r, ?_⟩
  show ((g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map (zAwayToZMod M q hMq) 1 0 =
    (N : ZMod M) * zAwayToZMod M q hMq r
  rw [Matrix.map_apply, hr, map_mul, map_natCast]

noncomputable def gamma0AwayToFin (hMq : Nat.Coprime M q) : Gamma0Away N q →* Gamma0Fin N M :=
  ((slAwayReduction M q hMq).comp (Gamma0Away N q).subtype).codRestrict (Gamma0Fin N M)
    (fun g => slAwayReduction_mem_Gamma0Fin N M q hMq g)

@[scoped simp]
theorem coe_gamma0AwayToFin (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    ((gamma0AwayToFin N M q hMq g : Gamma0Fin N M) : SL(2, ZMod M)) =
      slAwayReduction M q hMq (g : SL(2, ZAway q)) :=
  rfl

theorem gamma0FinUnitsChar_comp_gamma0AwayToFin (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q)
    (hNM : N ∣ M) :
    (gamma0FinUnitsChar N M hNM).comp (gamma0AwayToFin N M q hMq) = gamma0AwayUnitsChar N q hNq := by
  ext g
  rw [MonoidHom.comp_apply, gamma0FinUnitsChar_coe, gamma0AwayUnitsChar_coe, coe_gamma0AwayToFin,
    slAwayReduction_coe, Matrix.map_apply, ← RingHom.comp_apply, castHom_comp_zAwayToZMod N M q hMq hNq hNM]
  rfl

theorem mem_ker_gamma0AwayToFin_iff (hMq : Nat.Coprime M q) (g : Gamma0Away N q) :
    g ∈ (gamma0AwayToFin N M q hMq).ker ↔ (g : SL(2, ZAway q)) ∈ principalCongruenceAway M q hMq := by
  rw [MonoidHom.mem_ker, mem_principalCongruenceAway_iff, ← coe_gamma0AwayToFin]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem gamma0AwayToFin_vertexZeroAway (hMq : Nat.Coprime M q) (γ : Gamma0 N) :
    ((gamma0AwayToFin N M q hMq (vertexZeroAway N q γ) : Gamma0Fin N M) : SL(2, ZMod M)) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (γ : SL(2, ℤ)) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  show zAwayToZMod M q hMq (algebraMap ℤ (ZAway q) (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j)) =
    ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M)
  rw [zAwayToZMod_algebraMap]

theorem gamma0AwayToFin_surjective [NeZero M] (hMq : Nat.Coprime M q) (hNM : N ∣ M)
    (hSL : Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)))) :
    Function.Surjective (gamma0AwayToFin N M q hMq) := by
  intro g
  obtain ⟨γ, hγ⟩ := hSL (g : SL(2, ZMod M))
  obtain ⟨x, hx⟩ := g.2

  have h10 : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M)) = (N : ZMod M) * x := by
    rw [← hx, ← hγ]
    rfl
  have hN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have hval : (N : ZMod M) * x = (((N * x.val : ℕ) : ℤ) : ZMod M) := by
      rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hval, ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at h10
    have hNM' : (N : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.mpr hNM
    have h1 := dvd_add (hNM'.trans h10) (dvd_mul_right (N : ℤ) (x.val : ℤ))
    rwa [Nat.cast_mul, sub_add_cancel] at h1
  have hmem : γ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hN
  refine ⟨vertexZeroAway N q ⟨γ, hmem⟩, Subtype.ext ?_⟩
  rw [gamma0AwayToFin_vertexZeroAway, hγ]

end Bridge

section Factor

variable {N M q : ℕ} [NeZero M] (hMq : Nat.Coprime M q) (hNq : Nat.Coprime N q) (hNM : N ∣ M)
  {A : Type*} [AddCommGroup A]
  (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)

include hMq hNM h2 h3 in

theorem gamma0Away_hom_factor_of_ker_le (Ψ : Gamma0Away N q →* Multiplicative A)
    (hsurj : Function.Surjective (gamma0AwayToFin N M q hMq))
    (hker : (gamma0AwayToFin N M q hMq).ker ≤ Ψ.ker) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hNq) := by

  set Φ : Gamma0Fin N M →* Multiplicative A :=
    (gamma0AwayToFin N M q hMq).liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨Ψ, hker⟩ with hΦ
  have hΦΨ : Φ.comp (gamma0AwayToFin N M q hMq) = Ψ :=
    (gamma0AwayToFin N M q hMq).liftOfRightInverse_comp (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨Ψ, hker⟩
  obtain ⟨χ, hχ⟩ := gamma0Fin_hom_factor hNM h2 h3 Φ
  refine ⟨χ, ?_⟩
  rw [← hΦΨ, hχ, MonoidHom.comp_assoc, gamma0FinUnitsChar_comp_gamma0AwayToFin N M q hMq hNq hNM]

end Factor

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_A3_KillBridge
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_A3_Sep

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open DirectSum

theorem exists_addMonoidHom_zmod_primePow_ne_zero {B : Type*} [AddCommGroup B] [AddGroup.FG B]
    (h2 : ∀ b : B, b + b = 0 → b = 0) (h3 : ∀ b : B, b + b + b = 0 → b = 0) {b : B}
    (hb : b ≠ 0) : ∃ ℓ k : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ∃ φ : B →+ ZMod (ℓ ^ k), φ b ≠ 0 := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (G := B)
  have hfb : f b ≠ 0 := fun h => hb (by simpa using congrArg f.symm h)
  by_cases h1 : (f b).1 = 0
  ·
    have h2' : (f b).2 ≠ 0 := fun h => hfb (Prod.ext h1 h)
    obtain ⟨i, hi⟩ : ∃ i, (f b).2 i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact h2' (DFinsupp.ext h)
    have hpi := hp i
    have hei : e i ≠ 0 := by
      intro hzero
      apply hi
      haveI : Subsingleton (ZMod (p i ^ e i)) := ZMod.subsingleton_iff.mpr (by rw [hzero, pow_zero])
      exact Subsingleton.elim _ _

    have h5 : 5 ≤ p i := by
      by_contra hlt
      rw [not_le] at hlt
      have hp23 : p i = 2 ∨ p i = 3 := by
        have h2le := hpi.two_le
        have h4 : p i ≠ 4 := fun h => by rw [h] at hpi; exact absurd hpi (by decide)
        omega

      set t : ZMod (p i ^ e i) := ((p i ^ (e i - 1) : ℕ) : ZMod (p i ^ e i)) with ht
      have ht0 : t ≠ 0 := by
        rw [ht, Ne, ZMod.natCast_eq_zero_iff]
        intro hdvd
        have hlt' : p i ^ (e i - 1) < p i ^ e i :=
          Nat.pow_lt_pow_right hpi.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hei) one_pos)
        exact absurd (Nat.le_of_dvd (pow_pos hpi.pos _) hdvd) (not_le.mpr hlt')
      have hpt : p i • t = 0 := by
        rw [ht, nsmul_eq_mul, ← Nat.cast_mul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hei),
          ZMod.natCast_self]
      set y : B := f.symm (0, of (fun i => ZMod (p i ^ e i)) i t) with hy
      have hy0 : y ≠ 0 := by
        intro h0
        have h' : (0, of (fun i => ZMod (p i ^ e i)) i t) = (0 : (Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) := by
          rw [← f.apply_symm_apply (0, of _ i t), ← hy, h0, map_zero]
        have := congrArg (fun z : (Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i) => z.2 i) h'
        simp only [of_eq_same, Prod.snd_zero, DirectSum.zero_apply] at this
        exact ht0 this
      have hpy : p i • y = 0 := by
        apply f.injective
        rw [map_nsmul, hy, f.apply_symm_apply, map_zero, Prod.smul_mk, smul_zero, ← map_nsmul, hpt,
          map_zero, Prod.mk_zero_zero]
      rcases hp23 with h | h
      · refine hy0 (h2 y ?_)
        rw [h, two_nsmul] at hpy
        exact hpy
      · refine hy0 (h3 y ?_)
        rw [h, show (3 : ℕ) • y = y + y + y by abel] at hpy
        exact hpy
    refine ⟨p i, e i, hpi, h5,
      (DFinsupp.evalAddMonoidHom i).comp ((AddMonoidHom.snd _ _).comp f.toAddMonoidHom), ?_⟩
    simp at hi
    exact hi
  ·
    obtain ⟨j, hj⟩ : ∃ j, (f b).1 j ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact h1 (Finsupp.ext h)
    set v : ℤ := (f b).1 j with hv
    refine ⟨5, v.natAbs, Nat.prime_five, le_rfl,
      (Int.castAddHom (ZMod (5 ^ v.natAbs))).comp
        ((Finsupp.applyAddHom j).comp ((AddMonoidHom.fst _ _).comp f.toAddMonoidHom)), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_fst,
      AddEquiv.coe_toAddMonoidHom, Finsupp.applyAddHom_apply, Int.coe_castAddHom, ← hv]
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    apply hj
    refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 5)

theorem exists_monoidHom_zmod_primePow_ne_one {B : Type*} [CommGroup B] [Group.FG B]
    (h2 : ∀ b : B, b * b = 1 → b = 1) (h3 : ∀ b : B, b * b * b = 1 → b = 1) {b : B} (hb : b ≠ 1) :
    ∃ ℓ k : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ ∃ φ : B →* Multiplicative (ZMod (ℓ ^ k)), φ b ≠ 1 := by
  obtain ⟨ℓ, k, hℓ, h5, φ, hφ⟩ :=
    exists_addMonoidHom_zmod_primePow_ne_zero (B := Additive B)
      (fun x hx => h2 (Additive.toMul x) hx) (fun x hx => h3 (Additive.toMul x) hx)
      (b := Additive.ofMul b) hb
  refine ⟨ℓ, k, hℓ, h5,
    { toFun := fun x => Multiplicative.ofAdd (φ (Additive.ofMul x))
      map_one' := by simp
      map_mul' := fun x y => by simp [ofMul_mul] }, ?_⟩
  simpa using hφ

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_A3_Sep
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_Thm_IharaAmalgamEquiv

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open CongruenceSubgroup
open scoped MatrixGroups

noncomputable def amalgamEquiv (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) :
    iharaAmalgam N q ≃* Gamma0Away N q :=
  MulEquiv.ofBijective (amalgamToGamma0Away N q)
    ⟨amalgamToGamma0Away_injective hq hqN, amalgamToGamma0Away_surjective N q hqN hq⟩

@[scoped simp]
theorem amalgamEquiv_apply (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (x : iharaAmalgam N q) :
    amalgamEquiv N q hq hqN x = amalgamToGamma0Away N q x :=
  rfl

theorem coe_amalgamEquiv_vertex_zero (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    ((amalgamEquiv N q hq hqN (iharaVertex N q 0 g) : Gamma0Away N q) : SL(2, ZAway q)) =
      vertexZero N q g := by
  rw [amalgamEquiv_apply, coe_amalgamToGamma0Away, amalgamToAway_vertex_zero]

theorem coe_amalgamEquiv_vertex_one (N q : ℕ) (hq : q.Prime) (hqN : N.Coprime q) (g : Gamma0 N) :
    ((amalgamEquiv N q hq hqN (iharaVertex N q 1 g) : Gamma0Away N q) : SL(2, ZAway q)) =
      vertexOne N q g := by
  rw [amalgamEquiv_apply, coe_amalgamToGamma0Away, amalgamToAway_vertex_one]

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_Thm_IharaAmalgamEquiv
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_A3_Gamma0AwayFG

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open CongruenceSubgroup

open scoped MatrixGroups

scoped instance : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem fg_gamma0 (N : ℕ) [NeZero N] : Group.FG (Gamma0 N) :=
  inferInstance

theorem fg_iharaAmalgam (N q : ℕ) [NeZero N] : Group.FG (iharaAmalgam N q) := by
  have h0 : (iharaVertex N q 0).range.FG :=
    (Group.fg_iff_subgroup_fg _).mp (Group.fg_range _)
  have h1 : (iharaVertex N q 1).range.FG :=
    (Group.fg_iff_subgroup_fg _).mp (Group.fg_range _)
  refine ⟨?_⟩
  rw [← iharaVertex_range_sup N q]
  exact h0.sup h1

theorem fg_Gamma0Away (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : N.Coprime q) :
    Group.FG (Gamma0Away N q) := by
  haveI := fg_iharaAmalgam N q
  exact Group.fg_of_surjective (amalgamEquiv N q hq hqN).surjective

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_A3_Gamma0AwayFG
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_A3_Assembly

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Subgroup Matrix

open scoped MatrixGroups

section Arithmetic

theorem exists_coprime_split (s m : ℕ) (hm : m ≠ 0) :
    ∃ a b : ℕ, m = a * b ∧ Nat.Coprime a s ∧ Nat.Coprime a b ∧ ∀ p : ℕ, p.Prime → p ∣ b → p ∣ s := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 1, by norm_num, Nat.coprime_one_left _, Nat.coprime_one_left _,
      fun p hp hpb => absurd (Nat.le_of_dvd one_pos hpb) (by have := hp.two_le; omega)⟩
  | prime_pow p n hp hn =>
    by_cases hps : p ∣ s
    · refine ⟨1, p ^ n, by ring, Nat.coprime_one_left _, Nat.coprime_one_left _, fun r hr hrb => ?_⟩
      exact ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrb)) ▸ hps
    · refine ⟨p ^ n, 1, by ring, ?_, Nat.coprime_one_right _, fun r hr hrb => ?_⟩
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hps).pow_left n
      · exact absurd (Nat.le_of_dvd one_pos hrb) (by have := hr.two_le; omega)
  | coprime m n hm1 hn1 hmn ihm ihn =>
    obtain ⟨a₁, b₁, h₁, ha₁s, hab₁, hb₁⟩ := ihm (by omega)
    obtain ⟨a₂, b₂, h₂, ha₂s, hab₂, hb₂⟩ := ihn (by omega)
    refine ⟨a₁ * a₂, b₁ * b₂, by rw [h₁, h₂]; ring, Nat.Coprime.mul_left ha₁s ha₂s, ?_, ?_⟩
    · have ha₁m : a₁ ∣ m := ⟨b₁, h₁⟩
      have ha₂n : a₂ ∣ n := ⟨b₂, h₂⟩
      have hb₁m : b₁ ∣ m := ⟨a₁, by rw [h₁]; ring⟩
      have hb₂n : b₂ ∣ n := ⟨a₂, by rw [h₂]; ring⟩
      refine Nat.Coprime.mul_left (Nat.Coprime.mul_right hab₁ ?_) (Nat.Coprime.mul_right ?_ hab₂)
      · exact (hmn.coprime_dvd_left ha₁m).coprime_dvd_right hb₂n
      · exact (hmn.symm.coprime_dvd_left ha₂n).coprime_dvd_right hb₁m
    · intro p hp hpb
      rcases (Nat.Prime.dvd_mul hp).mp hpb with h | h
      · exact hb₁ p hp h
      · exact hb₂ p hp h

theorem exists_admissible_lift (s m : ℕ) (hs : s ≠ 0) (hm : m ≠ 0) :
    ∃ m' m₅ a b : ℕ, m ∣ m' * (m₅ * (2 ^ a * 3 ^ b)) ∧ Nat.Coprime m' s ∧
      Nat.Coprime m' (m₅ * (2 ^ a * 3 ^ b)) ∧ Nat.Coprime m₅ (2 ^ a * 3 ^ b) ∧ m' ∣ m ∧
      s ∣ m₅ * (2 ^ a * 3 ^ b) ∧ (∀ p : ℕ, p.Prime → p ∣ m₅ * (2 ^ a * 3 ^ b) → p ∣ s) ∧
      (∀ p : ℕ, p.Prime → p ∣ m₅ → 5 ≤ p) ∧ m₅ ≠ 0 := by
  obtain ⟨m', c, hmc, hm's, hm'c, hcs⟩ := exists_coprime_split s m hm

  set n := c * s with hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hmc
    exact hm hmc
  have hn0 : n ≠ 0 := Nat.mul_ne_zero hc0 hs
  set n₂ := ordCompl[2] n with hn₂
  have hn₂0 : n₂ ≠ 0 := (Nat.ordCompl_pos 2 hn0).ne'
  set m₅ := ordCompl[3] n₂ with hm₅
  have hm₅0 : m₅ ≠ 0 := (Nat.ordCompl_pos 3 hn₂0).ne'
  set a := n.factorization 2 with ha
  set b := n₂.factorization 3 with hb
  have hdecomp : m₅ * (2 ^ a * 3 ^ b) = n := by
    have h1 : 2 ^ a * n₂ = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have h2 : 3 ^ b * m₅ = n₂ := Nat.ordProj_mul_ordCompl_eq_self n₂ 3
    rw [← h1, ← h2]
    ring
  have h2m₅ : Nat.Coprime 2 m₅ :=
    (Nat.coprime_ordCompl Nat.prime_two hn0).coprime_dvd_right (Nat.ordCompl_dvd n₂ 3)
  have h3m₅ : Nat.Coprime 3 m₅ := Nat.coprime_ordCompl Nat.prime_three hn₂0
  refine ⟨m', m₅, a, b, ?_, hm's, ?_, ?_, ⟨c, hmc⟩, ?_, ?_, ?_, hm₅0⟩
  · rw [hdecomp, hmc, hn]
    exact mul_dvd_mul_left m' (dvd_mul_right c s)
  · rw [hdecomp, hn]
    exact Nat.Coprime.mul_right hm'c hm's
  · exact Nat.Coprime.mul_right (h2m₅.symm.pow_right a) (h3m₅.symm.pow_right b)
  · rw [hdecomp, hn]
    exact dvd_mul_left s c
  · intro p hp hpn
    rw [hdecomp, hn] at hpn
    rcases (Nat.Prime.dvd_mul hp).mp hpn with h | h
    · exact hcs p hp h
    · exact h
  · intro p hp hpm
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp h2m₅ hpm
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3m₅ hpm
    exact hp.five_le_of_ne_two_of_ne_three hp2 hp3

theorem coprime_sq_sub_one_self (q : ℕ) (hq : 1 ≤ q) : Nat.Coprime (q ^ 2 - 1) q := by
  have h : 1 + (q ^ 2 - 1) = q * q := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    rw [add_comm, Nat.sub_add_cancel this, pow_two]
  have h1 : Nat.Coprime (q * q) (q ^ 2 - 1) := by
    rw [← h]
    exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)
  exact (Nat.Coprime.coprime_dvd_left (dvd_mul_right q q) h1).symm

end Arithmetic
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Divisibility

variable (N q : ℕ)

theorem natCast_dvd_of_zAwayToZMod_eq_zero (hNq : Nat.Coprime N q) {z : ZAway q}
    (hz : zAwayToZMod N q hNq z = 0) : (N : ZAway q) ∣ z := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (q : ℤ)) z
  simp only at h
  have ha : ((a : ℤ) : ZMod N) = 0 := by
    have h' := congrArg (zAwayToZMod N q hNq) h
    rw [map_mul, hz, zero_mul, zAwayToZMod_algebraMap] at h'
    exact h'.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a N).mp ha
  have hs : IsUnit (algebraMap ℤ (ZAway q) s) := IsLocalization.map_units (ZAway q) s
  refine ⟨algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹, ?_⟩
  have hN : (N : ZAway q) = algebraMap ℤ (ZAway q) (N : ℤ) := by simp
  calc z = z * algebraMap ℤ (ZAway q) s * ↑hs.unit⁻¹ := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    _ = algebraMap ℤ (ZAway q) a * ↑hs.unit⁻¹ := by rw [h]
    _ = (N : ZAway q) * (algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹) := by
        rw [hb, map_mul, hN, mul_assoc]

theorem principalCongruenceAway_le_gamma0Away (hNq : Nat.Coprime N q) :
    principalCongruenceAway N q hNq ≤ Gamma0Away N q := by
  intro g hg
  rw [mem_principalCongruenceAway_iff] at hg
  rw [mem_Gamma0Away]
  refine natCast_dvd_of_zAwayToZMod_eq_zero N q hNq ?_
  have h := congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0) hg
  simp only [slAwayReduction_coe, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
  exact h

theorem dvd_of_slToAway_mennickeA_pow_mem_gamma0Away (hNq : Nat.Coprime N q) {m : ℕ}
    (hm : (slToAway q mennickeA) ^ m ∈ Gamma0Away N q) : N ∣ m := by
  rw [mem_Gamma0Away, slToAway_mennickeA_pow_coe] at hm
  have h10 : (!![1, 0; ((m : ℕ) : ZAway q), 1] : Matrix (Fin 2) (Fin 2) (ZAway q)) 1 0 = (m : ZAway q) := by
    simp
  rw [h10] at hm
  have h := map_dvd (zAwayToZMod N q hNq) hm
  rw [zAwayToZMod_natCast_self, map_natCast, zero_dvd_iff] at h
  exact (ZMod.natCast_eq_zero_iff m N).mp h

end Divisibility
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Level

variable (N q : ℕ)

theorem exists_level_mennickeQ_le [NeZero N] [NeZero q] (hNq : Nat.Coprime N q) (K : Subgroup (Gamma0Away N q))
    (hK : K.index ≠ 0) :
    ∃ m : ℕ, m ≠ 0 ∧ N ∣ m ∧ Nat.Coprime m q ∧ mennickeQ q m ≤ K.map (Gamma0Away N q).subtype := by

  set KG : Subgroup SL(2, ZAway q) := K.map (Gamma0Away N q).subtype with hKG
  have hΓidx : (Gamma0Away N q).index ≠ 0 := by
    have hle := principalCongruenceAway_le_gamma0Away N q hNq
    have hdvd := Subgroup.index_dvd_of_le hle
    have hNidx : (principalCongruenceAway N q hNq).index ≠ 0 := by
      show (slAwayReduction N q hNq).ker.index ≠ 0
      rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    exact fun h0 => hNidx (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hKGidx : KG.index ≠ 0 := by
    rw [hKG, Subgroup.index_map, Subgroup.ker_subtype, sup_bot_eq, Subgroup.range_subtype]
    exact Nat.mul_ne_zero hK hΓidx
  haveI : KG.FiniteIndex := ⟨hKGidx⟩

  set K' := KG.normalCore with hK'
  haveI : K'.Normal := Subgroup.normalCore_normal KG
  haveI : Finite (SL(2, ZAway q) ⧸ K') := Subgroup.finite_quotient_of_finiteIndex

  set a : SL(2, ZAway q) ⧸ K' := QuotientGroup.mk (slToAway q mennickeA) with ha
  set m := orderOf a with hm
  have hm0 : m ≠ 0 := (isOfFinOrder_of_finite a).orderOf_pos.ne'
  have hAm : (slToAway q mennickeA) ^ m ∈ K' := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← ha, hm]
    exact pow_orderOf_eq_one a
  have hQm : mennickeQ q m ≤ K' :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hAm)
  refine ⟨m, hm0, ?_, ?_, le_trans hQm (Subgroup.normalCore_le KG)⟩
  ·
    have hAΓ : (slToAway q mennickeA) ^ m ∈ Gamma0Away N q :=
      (Subgroup.map_subtype_le K) (Subgroup.normalCore_le KG (hQm (Subgroup.subset_normalClosure rfl)))
    exact dvd_of_slToAway_mennickeA_pow_mem_gamma0Away N q hNq hAΓ
  ·
    have hconj : (QuotientGroup.mk (mennickeU q) : SL(2, ZAway q) ⧸ K')⁻¹ * a * QuotientGroup.mk (mennickeU q) =
        a ^ (q ^ 2) := by
      rw [ha, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
        mennickeU_inv_mul_mennickeA_mul_mennickeU q]
    have hord : orderOf (a ^ (q ^ 2)) = m := by
      rw [← hconj]
      have h := MulEquiv.orderOf_eq (MulAut.conj (QuotientGroup.mk (mennickeU q) : SL(2, ZAway q) ⧸ K')⁻¹) a
      rw [MulAut.conj_apply, inv_inv] at h
      rw [h]
    have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 (NeZero.ne q)
    rw [orderOf_pow' a hq2, ← hm] at hord
    have hg : Nat.gcd m (q ^ 2) = 1 := by
      have hgpos : 0 < Nat.gcd m (q ^ 2) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hm0)
      have hmul : m / Nat.gcd m (q ^ 2) * Nat.gcd m (q ^ 2) = m := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      rw [hord] at hmul
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) (hmul.trans (mul_one m).symm)
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self q two_ne_zero) hg

end Level
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Assembly

variable {N q : ℕ}

theorem mem_of_coe_mem_map_subtype {Γ : Subgroup SL(2, ZAway q)} {K : Subgroup Γ} {g : Γ}
    (h : (g : SL(2, ZAway q)) ∈ K.map Γ.subtype) : g ∈ K := by
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp h
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

theorem zmod_primePow_two_torsion {ℓ k : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (x : ZMod (ℓ ^ k)) (hx : x + x = 0) :
    x = 0 := by
  have hu : IsUnit ((2 : ℕ) : ZMod (ℓ ^ k)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_primes Nat.prime_two hℓ |>.mpr (by omega)).pow_right k
  have h2 : ((2 : ℕ) : ZMod (ℓ ^ k)) * x = 0 := by rw [Nat.cast_two, two_mul, hx]
  exact (hu.mul_right_eq_zero).mp h2

theorem zmod_primePow_three_torsion {ℓ k : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (x : ZMod (ℓ ^ k))
    (hx : x + x + x = 0) : x = 0 := by
  have hu : IsUnit ((3 : ℕ) : ZMod (ℓ ^ k)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_primes Nat.prime_three hℓ |>.mpr (by omega)).pow_right k
  have h3 : ((3 : ℕ) : ZMod (ℓ ^ k)) * x = 0 := by
    rw [Nat.cast_ofNat]
    have : (3 : ZMod (ℓ ^ k)) * x = x + x + x := by ring
    rw [this, hx]
  exact (hu.mul_right_eq_zero).mp h3

private theorem slAwayReduction_surjective_of_int (m : ℕ) (hmq : Nat.Coprime m q)
    (hSLm : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod m)))) :
    Function.Surjective (slAwayReduction m q hmq) := by
  intro Y
  obtain ⟨g, hg⟩ := hSLm Y
  refine ⟨slToAway q g, ?_⟩
  rw [← hg]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slAwayReduction_coe, coe_slToAway, Matrix.map_map]
  show zAwayToZMod m q hmq (algebraMap ℤ (ZAway q) (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j)) =
    ((((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod m)
  rw [zAwayToZMod_algebraMap]

theorem exists_level_ker_le (hq : q.Prime) (hqN : Nat.Coprime N q) [NeZero N]
    (hSL : ∀ (M : ℕ) [NeZero M],
      Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))))
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → _root_.commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hHabel : ∀ (m : ℕ) (hmq : Nat.Coprime m q),
      principalCongruenceAway m q hmq ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    {ℓ k : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (Ψ' : Gamma0Away N q →* Multiplicative (ZMod (ℓ ^ k))) :
    ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ N ∣ M ∧
      ∀ g : Gamma0Away N q, (g : SL(2, ZAway q)) ∈ principalCongruenceAway M q hMq → Ψ' g = 1 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.ne_zero⟩
  have hq2 : 2 ≤ q := hq.two_le

  have hKidx : Ψ'.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  obtain ⟨m, hm0, hNm, hmq, hQm⟩ := exists_level_mennickeQ_le N q hqN Ψ'.ker hKidx

  set s := q ^ 2 - 1 with hs
  have hs0 : s ≠ 0 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hsq : Nat.Coprime s q := coprime_sq_sub_one_self q (by omega)
  obtain ⟨m', m₅, a, b, hmM, hm's, hm'M, h56, hm'm, hsM, hsat, h5M, hm₅0⟩ := exists_admissible_lift s m hs0 hm0
  set m₆ := 2 ^ a * 3 ^ b with hm₆
  have hm₆0 : m₆ ≠ 0 := by positivity
  have hm'0 : m' ≠ 0 := fun h => hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hm'm))
  haveI : NeZero m' := ⟨hm'0⟩
  haveI : NeZero m₅ := ⟨hm₅0⟩
  haveI : NeZero m₆ := ⟨hm₆0⟩
  haveI : NeZero (m₅ * m₆) := ⟨Nat.mul_ne_zero hm₅0 hm₆0⟩
  have hm'q : Nat.Coprime m' q := hmq.coprime_dvd_left hm'm
  have hm''q : Nat.Coprime (m₅ * m₆) q := by
    refine Nat.coprime_of_dvd fun p hp hpM hpq => ?_
    have hps : p ∣ s := hsat p hp hpM
    have h1 : p ∣ Nat.gcd s q := Nat.dvd_gcd hps hpq
    rw [hsq.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hMq : Nat.Coprime (m' * (m₅ * m₆)) q := Nat.Coprime.mul_left hm'q hm''q
  have hM0 : m' * (m₅ * m₆) ≠ 0 := Nat.mul_ne_zero hm'0 (Nat.mul_ne_zero hm₅0 hm₆0)
  refine ⟨m' * (m₅ * m₆), hMq, hM0, hNm.trans hmM, ?_⟩

  have hN' : MennickeCSP m' q hm'q := by
    exact mennickeCSP_of_coprime_of_stem q m' hm'q hm's (hHabel m' hm'q)
      (slAwayReduction_surjective_of_int m' hm'q (hSL m'))
      (commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod hP1 hP2 m'
        (fun p hp hpm => five_le_of_prime_dvd_block q m' hp hpm hm'q hm's)).2
  have hZ'' : mennickeZ q (m₅ * m₆) hm''q = ⊤ :=
    ihxw14_dio_lemma22_statement_unconditional q hq2 (m₅ * m₆) hm''q hsM hsat
  have hsurj'' : Function.Surjective (slAwayReduction (m₅ * m₆) q hm''q) :=
    slAwayReduction_surjective_of_int (m₅ * m₆) hm''q (hSL (m₅ * m₆))
  have hsurj' : Function.Surjective (slAwayReduction m' q hm'q) :=
    slAwayReduction_surjective_of_int m' hm'q (hSL m')
  have hQM : mennickeQ q (m' * (m₅ * m₆)) ≤ Ψ'.ker.map (Gamma0Away N q).subtype :=
    le_trans (mennickeQ_le_of_dvd q m (m' * (m₅ * m₆)) hmM) hQm
  intro g hg

  have hpow : (g : SL(2, ZAway q)) ^ Nat.card (SL(2, ZMod m₆)) ∈ mennickeQ q (m' * (m₅ * m₆)) :=
    pow_card_mem_mennickeQ_mul q m' m₅ m₆ hm'M h56 hm'q hm''q hMq hm's hsM h5M hP1 hP2 hN' hsurj' hZ''
      (hHabel (m₅ * m₆) hm''q) hsurj'' hg
  have hker_n : g ^ Nat.card (SL(2, ZMod m₆)) ∈ Ψ'.ker :=
    mem_of_coe_mem_map_subtype (by rw [Subgroup.coe_pow]; exact hQM hpow)
  have h1 : Ψ' g ^ Nat.card (SL(2, ZMod m₆)) = 1 := by
    rw [← map_pow]
    exact hker_n
  have h2 : Ψ' g ^ (ℓ ^ k) = 1 := by
    have h := pow_card_eq_one' (x := Ψ' g)
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h

  have hcop : Nat.Coprime (Nat.card (SL(2, ZMod m₆))) (ℓ ^ k) := by
    refine Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdvd => ?_))
    rcases prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow a b hℓ hdvd with h | h <;> omega
  have h : Ψ' g ^ Nat.gcd (Nat.card (SL(2, ZMod m₆))) (ℓ ^ k) = 1 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

theorem gamma0Away_hom_factor_of_inputs (hq : q.Prime) (hqN : Nat.Coprime N q)
    (hSL : ∀ (M : ℕ) [NeZero M],
      Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))))
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → _root_.commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (hHabel : ∀ (m : ℕ) (hmq : Nat.Coprime m q),
      principalCongruenceAway m q hmq ≤ _root_.commutator (SL(2, ZAway q)) ⊔ mennickeQ q m)
    {A : Type*} [AddCommGroup A] (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Ψ : Gamma0Away N q →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hqN) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hq.one_lt.ne' (Nat.coprime_zero_left q |>.mp hqN)
  haveI : NeZero N := ⟨hN0⟩
  have hsurjN : Function.Surjective (gamma0AwayToFin N N q hqN) :=
    gamma0AwayToFin_surjective N N q hqN (dvd_refl N) (hSL N)
  refine gamma0Away_hom_factor_of_ker_le hqN hqN (dvd_refl N) h2 h3 Ψ hsurjN ?_

  intro γ hγ
  rw [MonoidHom.mem_ker]
  by_contra hne

  haveI : Group.FG (Gamma0Away N q) := fg_Gamma0Away N q hq hqN
  have hB2 : ∀ b : Ψ.range, b * b = 1 → b = 1 := by
    intro b hb
    apply Subtype.ext
    have hb' : ((b : Multiplicative A) * b : Multiplicative A) = 1 := by exact_mod_cast congrArg Subtype.val hb
    exact h2 (Multiplicative.toAdd (b : Multiplicative A)) hb'
  have hB3 : ∀ b : Ψ.range, b * b * b = 1 → b = 1 := by
    intro b hb
    apply Subtype.ext
    have hb' : ((b : Multiplicative A) * b * b : Multiplicative A) = 1 := by exact_mod_cast congrArg Subtype.val hb
    exact h3 (Multiplicative.toAdd (b : Multiplicative A)) hb'
  have hbne : Ψ.rangeRestrict γ ≠ 1 := by
    intro h
    apply hne
    have := congrArg Subtype.val h
    rwa [MonoidHom.coe_rangeRestrict] at this
  obtain ⟨ℓ, k, hℓ, h5, φ, hφ⟩ := exists_monoidHom_zmod_primePow_ne_one hB2 hB3 hbne
  set Ψ' : Gamma0Away N q →* Multiplicative (ZMod (ℓ ^ k)) := φ.comp Ψ.rangeRestrict with hΨ'
  have hΨ'γ : Ψ' γ ≠ 1 := hφ

  obtain ⟨M, hMq, hM0, hNM, hkill⟩ := exists_level_ker_le hq hqN hSL hP1 hP2 hHabel hℓ h5 Ψ'
  haveI : NeZero M := ⟨hM0⟩

  have hsurjM : Function.Surjective (gamma0AwayToFin N M q hMq) :=
    gamma0AwayToFin_surjective N M q hMq hNM (hSL M)
  have hkerM : (gamma0AwayToFin N M q hMq).ker ≤ Ψ'.ker := by
    intro g hg
    rw [mem_ker_gamma0AwayToFin_iff] at hg
    exact hkill g hg
  obtain ⟨χ', hχ'⟩ := gamma0Away_hom_factor_of_ker_le hMq hqN hNM (zmod_primePow_two_torsion hℓ h5)
    (zmod_primePow_three_torsion hℓ h5) Ψ' hsurjM hkerM
  apply hΨ'γ
  have hchar : gamma0AwayUnitsChar N q hqN γ = 1 := by
    rw [← gamma0FinUnitsChar_comp_gamma0AwayToFin N N q hqN hqN (dvd_refl N), MonoidHom.comp_apply,
      (MonoidHom.mem_ker).mp hγ, map_one]
  rw [hχ', MonoidHom.comp_apply, hchar, map_one]

end Assembly
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_A3_Assembly
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_A3_SL2Surjective

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

section ArithmeticLemmas

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by

  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]
    split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]
    split
    · next h => simp [h]
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd
    refine H p pp ?_ hpd
    rw [hγ_def] at hpγ
    by_cases h : c₀ = 0
    · simp [h]
    · rwa [if_neg h] at hpγ

  refine ⟨γ, d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ), ?_, hγc, ?_⟩
  ·
    by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd
        rwa [add_sub_cancel_left] at this
      rcases (Nat.prime_iff_prime_int.mp pp).dvd_or_dvd h3 with h4 | h4
      · exact not_dvd_primeSel pp hpd (natCast_dvd_int.mp h4)
      · exact Hγ p pp h1 hpd h4
    ·
      have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ))
      rwa [add_sub_cancel_right] at this
  ·
    push_cast
    simp

end ArithmeticLemmas
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Lifting

theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by

  set a₀ : ℤ := ZMod.cast a with ha₀
  set b₀ : ℤ := ZMod.cast b with hb₀
  set c₀ : ℤ := ZMod.cast c with hc₀
  set d₀ : ℤ := ZMod.cast d with hd₀
  have hcasta : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcastb : ((b₀ : ℤ) : ZMod N) = b := ZMod.intCast_zmod_cast b
  have hcastc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c
  have hcastd : ((d₀ : ℤ) : ZMod N) = d := ZMod.intCast_zmod_cast d

  have hdvd : (N : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcasta, hcastb, hcastc, hcastd]
    rw [sub_eq_zero]
    exact h

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpc hpd hpN
    have hone : (p : ℤ) ∣ 1 := by
      have h1 : (p : ℤ) ∣ a₀ * d₀ - b₀ * c₀ - 1 := hpN.trans hdvd
      have h2 : (p : ℤ) ∣ a₀ * d₀ := hpd.mul_left a₀
      have h3 : (p : ℤ) ∣ b₀ * c₀ := hpc.mul_left b₀
      have key : (1 : ℤ) = a₀ * d₀ - b₀ * c₀ - (a₀ * d₀ - b₀ * c₀ - 1) := by ring
      rw [key]
      exact (h2.sub h3).sub h1
    exact pp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast hone))

  obtain ⟨γ, δ, hγδ, hγ, hδ⟩ := exists_coprime_lift N H
  rw [hcastc] at hγ
  rw [hcastd] at hδ

  set α₀ : ℤ := Int.gcdB γ δ with hα₀
  set β₀ : ℤ := -Int.gcdA γ δ with hβ₀
  have hdet₀ : α₀ * δ - β₀ * γ = 1 := by
    have hbez := Int.gcd_eq_gcd_ab γ δ
    rw [hγδ] at hbez
    push_cast at hbez
    rw [hα₀, hβ₀]
    linear_combination -hbez

  have hdet₀' : (α₀ : ZMod N) * d - (β₀ : ZMod N) * c = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₀
    push_cast at this
    rwa [hγ, hδ] at this

  set lam : ZMod N := b * (α₀ : ZMod N) - a * (β₀ : ZMod N) with hlam
  set l : ℤ := ZMod.cast lam with hl
  have hcastl : ((l : ℤ) : ZMod N) = lam := ZMod.intCast_zmod_cast lam
  refine ⟨α₀ + l * γ, β₀ + l * δ, γ, δ, ?_, ?_, ?_, hγ, hδ⟩
  · linear_combination hdet₀
  ·
    push_cast
    rw [hcastl, hγ, hlam]
    linear_combination (-(α₀ : ZMod N)) * h + a * hdet₀'
  ·
    push_cast
    rw [hcastl, hδ, hlam]
    linear_combination (-(β₀ : ZMod N)) * h + b * hdet₀'

theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  intro M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have hM := M.prop
    rwa [Matrix.det_fin_two] at hM
  obtain ⟨α, β, γ, δ, h1, ha, hb, hc, hd⟩ := exists_sl2_int_lift hdet
  refine ⟨⟨!![α, β; γ, δ], by rw [Matrix.det_fin_two_of]; exact h1⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simpa [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
      using ‹_›

end Lifting
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_A3_SL2Surjective
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

section Inl_Thm_IharaA3_FINAL

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "mennickeA mennickeA_coe mennickeA_pow_coe slAwayReduction slAwayReduction_coe principalCongruenceAway mem_principalCongruenceAway_iff MennickeCSP qInv qInv_mul_natCast_q mennickeU mennickeU_coe mennickeQ mennickeZ MennickeLemma21 ZAway Gamma0Away mem_Gamma0Away slToAway coe_slToAway vertexZero vertexOne amalgamToAway_vertex_zero amalgamToAway_vertex_one amalgamToGamma0Away coe_amalgamToGamma0Away iharaAmalgam iharaVertex iharaVertex_range_sup zAwayToZMod zAwayToZMod_algebraMap zAwayToZMod_natCast_self gamma0AwayUnitsChar gamma0AwayUnitsChar_coe vertexZeroAway gamma0Fin_hom_factor Gamma0Fin gamma0FinUnitsChar gamma0FinUnitsChar_coe amalgamToGamma0Away_injective amalgamToGamma0Away_surjective mennickeCSP_of_coprime_of_stem HasTrivialSchurMultiplier pow_card_mem_mennickeQ_mul commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow ihxw14_dio_lemma22_statement_unconditional principalCongruenceAway_le_commutator_sup_mennickeQ hasTrivialSchurMultiplier_SL2_ZMod_prime_pow isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open scoped MatrixGroups

theorem gamma0Away_hom_factor_impl {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q)
    {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Ψ : Gamma0Away N q →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hqN) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  exact gamma0Away_hom_factor_of_inputs hq hqN
    (fun M hM => @SL2_reduction_surjective M hM)
    (fun p n hp h5 hn => Group.isPerfect_def.mp (isPerfect_SL2_ZMod_prime_pow hp h5 hn))
    (fun p n hp h5 hn => hasTrivialSchurMultiplier_SL2_ZMod_prime_pow hp h5 hn)
    (fun m hmq => principalCongruenceAway_le_commutator_sup_mennickeQ m q hmq)
    h2 h3 Ψ

end Ihara
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

end Inl_Thm_IharaA3_FINAL
p2m_reactivate "P2MW.S_Ihara_gamma0Away_hom_factor.Ihara"

theorem solution {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q)
    {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Ψ : Ihara.Gamma0Away N q →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (Ihara.gamma0AwayUnitsChar N q hqN) :=
  Ihara.gamma0Away_hom_factor_impl hq hqN h2 h3 Ψ

end S_Ihara_gamma0Away_hom_factor
end P2MW
export P2MW.S_Ihara_gamma0Away_hom_factor (solution)
