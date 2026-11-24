-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.adjoint_repOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:09.743877+00:00
-- url     : https://prove2.me/submissions/92954845-e015-4539-b2e7-0323fe68d341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_inner_apply_left
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_inner_repOp

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
variable [MeasurableSpace G]
variable {π : G →* (H →L[ℂ] H)} {μ : Measure G} {f f' : G → ℂ}
variable [OpensMeasurableSpace G] [IsFiniteMeasureOnCompacts μ]
namespace GlobalTheory.OpTrace
namespace IsUnitaryRep
theorem _root_.solution [IsTopologicalGroup G] [BorelSpace G] [μ.IsInvInvariant]
    (hπ : IsUnitaryRep π) (hf : Continuous f) (hc : HasCompactSupport f) :
    adjoint (repOp π μ f) = repOp π μ fun g => starRingEnd ℂ (f g⁻¹) := by
  have hf' : Continuous fun g => starRingEnd ℂ (f g⁻¹) :=
    Complex.continuous_conj.comp (hf.comp continuous_inv)
  have hc' : HasCompactSupport fun g => starRingEnd ℂ (f g⁻¹) :=
    (hc.comp_homeomorph (Homeomorph.inv G)).comp_left (g := starRingEnd ℂ) (map_zero _)
  ext v
  refine ext_inner_left ℂ fun w => ?_
  rw [adjoint_inner_right, hπ.inner_repOp hf' hc', ← inner_conj_symm, hπ.inner_repOp hf hc,
    ← integral_conj, ← integral_inv_eq_self]
  simp only [map_mul, inner_conj_symm, hπ.inner_apply_left, inv_inv]
end IsUnitaryRep
end GlobalTheory.OpTrace
