-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness.orthogonalBranchSum_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/f5e9513f-bec6-476e-b034-9b6aadf31a89

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
theorem _root_.solution
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0) :
    Function.Injective (orthogonalBranchSum f) := by
  classical
  intro x y heq
  let z : (i : ι) → E i := x - y
  have hz : orthogonalBranchSum f z = 0 := by
    dsimp [z]
    rw [map_sub, heq, sub_self]
  apply funext
  intro i
  have hsingle :
      (∑ j : ι, ⟪f i (z i), f j (z j)⟫_ℝ) =
        ⟪f i (z i), f i (z i)⟫_ℝ := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact horth i j (Ne.symm hji) (z i) (z j)
    · simp
  have hinner : ⟪f i (z i), f i (z i)⟫_ℝ = 0 := by
    calc
      ⟪f i (z i), f i (z i)⟫_ℝ =
          ∑ j : ι, ⟪f i (z i), f j (z j)⟫_ℝ := hsingle.symm
      _ = ⟪f i (z i), orthogonalBranchSum f z⟫_ℝ := by
        rw [orthogonalBranchSum_apply, inner_sum]
      _ = 0 := by rw [hz, inner_zero_right]
  have hzi : z i = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp <| by
    calc
      ⟪z i, z i⟫_ℝ = ⟪f i (z i), f i (z i)⟫_ℝ :=
        ((f i).inner_map_map (z i) (z i)).symm
      _ = 0 := hinner
  change x i - y i = 0 at hzi
  exact sub_eq_zero.mp hzi
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
