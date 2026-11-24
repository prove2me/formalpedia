-- Prove2me | solution 1 for GlobalTheory.DetIdeal.det_mul_vol_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:02.077062+00:00
-- url     : https://prove2.me/submissions/2e50db4b-cae9-4782-b4f7-3ca07135ebab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Theorems.Thm_GlobalTheory_DetIdeal_det_mem_pow

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
theorem _root_.solution (c : FractionalIdeal R⁰ K) (L L' : Set (Fin r → R)) (A : Matrix (Fin r) (Fin r) K)
    (h : ∀ x ∈ L, ∀ y ∈ L', (algebraMap R K ∘ x) ⬝ᵥ A *ᵥ (algebraMap R K ∘ y) ∈ c) :
    FractionalIdeal.spanSingleton R⁰ A.det * ((vol L * vol L' : Ideal R) : FractionalIdeal R⁰ K) ≤ c ^ r := by
  have key : ∀ z ∈ vol L * vol L', A.det * algebraMap R K z ∈ ((c ^ r : FractionalIdeal R⁰ K) : Submodule R K) := by
    intro z hz
    unfold vol at hz
    rw [Ideal.span_mul_span'] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨_, ⟨X, hX, rfl⟩, _, ⟨Y, hY, rfl⟩, rfl⟩ := hz
      have := det_mem_pow c (X.map (algebraMap R K) * A * (Y.map (algebraMap R K))ᵀ) fun i j => by
        have := h _ (hX i) _ (hY j)
        convert this using 1
        rw [Matrix.mul_assoc]
        simp [Matrix.mul_apply, dotProduct, Matrix.mulVec]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
      rw [FractionalIdeal.mem_coe]
      convert this using 1
      simp only [map_mul, RingHom.map_det, RingHom.mapMatrix_apply]
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, mul_add]; exact Submodule.add_mem _ hx hy
    | smul t x _ hx =>
      rw [smul_eq_mul, map_mul, mul_left_comm, ← Algebra.smul_def]; exact Submodule.smul_mem _ t hx
  rw [FractionalIdeal.mul_le]
  intro a ha b hb
  obtain ⟨t, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp ha
  obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hb
  rw [smul_mul_assoc, ← FractionalIdeal.mem_coe]
  exact Submodule.smul_mem _ t (key z hz)
end GlobalTheory.DetIdeal
