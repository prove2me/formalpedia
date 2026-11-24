-- Prove2me | solution 1 for GlobalTheory.PRep.IsSmooth.isLocallyConstant_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.942803+00:00
-- url     : https://prove2.me/submissions/5a506712-d6be-40c3-b0be-6042ac275f4b

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
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsSmooth
theorem _root_.solution [ContinuousMul G] {ρ : Representation ℂ G V}
    (hρ : IsSmooth ρ) (v : V) : IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {k | ρ k v = v},
    (hρ v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have : ρ g (ρ (g⁻¹ * x) v) = ρ g v := congrArg _ hx
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at this
end _root_.GlobalTheory.PRep.IsSmooth
end GlobalTheory.OpTrace
