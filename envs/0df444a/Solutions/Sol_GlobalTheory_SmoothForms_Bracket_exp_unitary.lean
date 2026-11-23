-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Bracket.exp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:57.034428+00:00
-- url     : https://prove2.me/submissions/ff3a3f5b-dae7-45a7-9f45-7a8774eae3f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
namespace GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
private theorem isLieData_map_pow (H : IsLieData σ j s) (x : 𝔸) (n : ℕ) : σ (x ^ n) = σ x ^ n := by
  induction n with
  | zero => simpa using H.one
  | succ n ih => rw [pow_succ, H.anti, ih, pow_succ']
private theorem isLieData_map_exp (H : IsLieData σ j s) (x : 𝔸) :
    σ (NormedSpace.exp x) = NormedSpace.exp (σ x) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  rw [NormedSpace.exp_eq_tsum ℝ]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℝ) x
  have := (LinearMap.toContinuousLinearMap σ).map_tsum hs
  simpa [LinearMap.coe_toContinuousLinearMap', map_smul, isLieData_map_pow H] using this
end GlobalTheory.SmoothForms.Bracket
end

set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Bracket
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.Bracket
theorem _root_.solution (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hb : ∀ y : 𝔸, y ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := fun y =>
    (NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  rw [isLieData_map_exp H, (H.skew (j X)).2 ⟨X, rfl⟩,
    ← NormedSpace.exp_add_of_commute_of_mem_ball (Commute.neg_left (Commute.refl _)) (hb _) (hb _),
    neg_add_cancel, NormedSpace.exp_zero]
end GlobalTheory.SmoothForms.Bracket
