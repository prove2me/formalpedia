-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.inner_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:44.848828+00:00
-- url     : https://prove2.me/submissions/a552a23d-bbc1-45ea-9d7d-e9e46147f31f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GlobalTheory.OpTrace
namespace IsUnitaryRep
theorem _root_.solution {π : G →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) (g : G)
    (v w : H) : ⟪π g v, w⟫_ℂ = ⟪v, π g⁻¹ w⟫_ℂ := by
  let U : H →ₗᵢ[ℂ] H := ⟨(π g : H →ₗ[ℂ] H), hπ.norm_apply g⟩
  have h1 : π g (π g⁻¹ w) = w := by
    have : π g * π g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun S : H →L[ℂ] H => S w) this
  conv_lhs => rw [← h1]
  exact U.inner_map_map v (π g⁻¹ w)
end IsUnitaryRep
end GlobalTheory.OpTrace
