-- Prove2me | solution 1 for GlobalTheory.OpTrace.finRankTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:32.433729+00:00
-- url     : https://prove2.me/submissions/8da89a9d-738e-4a64-8020-18872b7caa0f

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution (T : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ x, T x ∈ W) :
    finRankTrace T = LinearMap.trace ℂ W (T.restrict fun x _ => hW x) := by
  have hle : LinearMap.range T ≤ W := by rintro _ ⟨x, rfl⟩; exact hW x
  have := Submodule.finiteDimensional_of_le hle
  exact LinearMap.trace_comp_comm' (Submodule.inclusion hle) (T.rangeRestrict ∘ₗ W.subtype)
end GlobalTheory.OpTrace
