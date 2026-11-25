-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_mul_vol_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:30.100925+00:00
-- url     : https://prove2.me/submissions/91d9e701-74cf-45e9-a58b-1590e11185c5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_det_mem_vol
import Theorems.Thm_P2M_GlobalTheory_DetIdeal_pow_mem_pow__741349ce2029
import Theorems.Thm_GlobalTheory_DetIdeal_exists_local_generator
import Theorems.Thm_GlobalTheory_DetIdeal_det_mul_vol_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.DetIdeal
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] {r : ℕ}
namespace GlobalTheory.DetIdeal
theorem _root_.solution (c : FractionalIdeal R⁰ K) (hc : c ≠ 0) (L L' : Set (Fin r → R))
    (A : Matrix (Fin r) (Fin r) K) (hA : A.det ≠ 0) (hL' : vol L' ≠ ⊥)
    (h : ∀ v : Fin r → K, (∀ y ∈ L', v ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) ∈ c) ↔ ∃ x ∈ L, algebraMap R K ∘ x = v) :
    FractionalIdeal.spanSingleton R⁰ A.det * ((vol L * vol L' : Ideal R) : FractionalIdeal R⁰ K) = c ^ r := by
  have hle := det_mul_vol_le c L L' A fun x hx => (h _).mpr ⟨x, hx, rfl⟩
  set W := FractionalIdeal.spanSingleton R⁰ A.det * ((vol L * vol L' : Ideal R) : FractionalIdeal R⁰ K) with hW
  have hle1 : W * c⁻¹ ^ r ≤ 1 := by
    calc W * c⁻¹ ^ r ≤ c ^ r * c⁻¹ ^ r := by gcongr
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  suffices hJ1 : J = ⊤ by
    rw [hJ1, FractionalIdeal.coeIdeal_top, inv_pow] at hJ
    exact (mul_inv_eq_one₀ (pow_ne_zero _ hc)).mp hJ.symm
  by_contra hJ1
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ1
  obtain ⟨t, ht, w, hw, s', hs', hs'e⟩ :=
    exists_local_generator c hc (c : Submodule R K) (Submodule.span_eq _).symm P hP.ne_top
  obtain ⟨_, ⟨_, ⟨Y, hY, rfl⟩, rfl⟩, u, hu, s, hs, hse⟩ :=
    exists_local_generator ((vol L' : Ideal R) : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hL') (algebraMap R K '' _)
      (by rw [FractionalIdeal.coe_coeIdeal, vol, IsLocalization.coeSubmodule_span]) P hP.ne_top
  set Yk := Y.map (algebraMap R K) with hYk
  have hdetY : algebraMap R K Y.det = Yk.det := RingHom.map_det _ _
  set Xk : Matrix (Fin r) (Fin r) K := (u * t) • (adjugate Ykᵀ * A⁻¹) with hXk
  have hXA : Xk * A = (u * t) • adjugate Ykᵀ := by
    rw [hXk, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hA), Matrix.mul_one]
  have hrows : ∀ i, ∃ x ∈ L, algebraMap R K ∘ x = Xk i := fun i => by
    rw [← h]
    intro y hy
    have e1 : Xk i ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) = t * (algebraMap R K (Y.updateRow i y).det * u) := by
      have : Xk i ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) = ((Xk * A) *ᵥ (algebraMap R K ∘ y)) i := by
        rw [← Matrix.mulVec_mulVec]; rfl
      rw [this, hXA, Matrix.smul_mulVec, ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply,
        Matrix.cramer_transpose_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_updateRow,
        smul_eq_mul]
      ring
    have hmem : (Y.updateRow i y).det ∈ vol L' := det_mem_vol fun j => by
      by_cases hj : j = i
      · rw [hj, Matrix.updateRow_self]; exact hy
      · rw [Matrix.updateRow_ne hj]; exact hY j
    have h1 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem R⁰ (P := K) hmem) hu
    rw [mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr hL')] at h1
    have h2 := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp ht) h1
    rw [mul_one] at h2
    rw [e1]; exact h2
  choose X hX hXe using hrows
  have hdetX : algebraMap R K (Matrix.of X).det = Xk.det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact congrFun (hXe i) j
  have hmemW : (u * t * Yk.det) ^ r ∈ W := by
    have e : (u * t * Yk.det) ^ r = A.det * algebraMap R K ((Matrix.of X).det * Y.det) := by
      rw [map_mul, hdetX, hdetY]
      have : (Xk * A * Ykᵀ).det = (u * t * Yk.det) ^ r := by
        rw [hXA, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, Matrix.det_smul, Matrix.det_one,
          Matrix.det_transpose, mul_one, Fintype.card_fin]
      rw [← this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    rw [e]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mul_mem_mul (det_mem_vol hX) (det_mem_vol hY)))
  have h3 := FractionalIdeal.mul_mem_mul hmemW (pow_mem_pow' _ hw r)
  have e3 : (u * t * Yk.det) ^ r * w ^ r = algebraMap R K ((s * s') ^ r) := by
    rw [map_pow, map_mul, hse, hs'e, hdetY, ← mul_pow]
    congr 1; ring
  rw [← hJ, e3] at h3
  obtain ⟨z, hz, hze⟩ := (FractionalIdeal.mem_coeIdeal _).mp h3
  rw [IsFractionRing.injective R K hze] at hz
  rcases hP.isPrime.mem_or_mem (hP.isPrime.mem_of_pow_mem _ (hJP hz)) with h' | h'
  · exact hs h'
  · exact hs' h'
end GlobalTheory.DetIdeal
