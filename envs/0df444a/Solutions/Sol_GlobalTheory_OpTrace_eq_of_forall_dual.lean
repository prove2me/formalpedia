-- Prove2me | solution 1 for GlobalTheory.OpTrace.eq_of_forall_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:01.037191+00:00
-- url     : https://prove2.me/submissions/399521a8-ae77-473a-8ccd-cea1a5e2124b

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
variable {X V : Type*} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace X]
variable [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
omit [MeasurableSpace X] [OpensMeasurableSpace X]
namespace GlobalTheory.OpTrace
theorem _root_.solution {v w : V} (h : ∀ l : V →ₗ[ℂ] ℂ, l v = l w) : v = w := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, h l, sub_self]
end GlobalTheory.OpTrace
