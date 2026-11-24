-- Prove2me | solution 1 for GlobalTheory.OpTrace.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:46.892819+00:00
-- url     : https://prove2.me/submissions/66543b32-d1fe-46fd-ae70-2ad9232cc721

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
omit [Module ℂ V]
namespace GlobalTheory.OpTrace
theorem _root_.solution {F : X → V} (hF : IsLocallyConstant F) (hc : HasCompactSupport F) :
    (Set.range F).Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun w => F ⁻¹' {w}) (fun w => hF _)
    fun x _ => Set.mem_iUnion.2 ⟨F x, rfl⟩
  refine (t.finite_toSet.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : F x = 0
  · exact Or.inl hx
  · simpa using Or.inr (by simpa using ht (subset_tsupport F hx))
end GlobalTheory.OpTrace
