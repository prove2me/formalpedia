-- Prove2me | solution 1 for GlobalTheory.OpTrace.IsUnitaryRep.repTrace_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:24.810387+00:00
-- url     : https://prove2.me/submissions/8b2b8412-f491-44a9-a491-48b0c6f60312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_comp
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_trace_conj
import Theorems.Thm_GlobalTheory_OpTrace_IsUnitaryRep_comp_repOp

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
theorem _root_.solution {π' : G →* (K →L[ℂ] K)} (hπ : IsUnitaryRep π)
    (hπ' : IsUnitaryRep π') (hf : Continuous f) (hc : HasCompactSupport f) (A : H ≃L[ℂ] K)
    (hA : ∀ g v, A (π g v) = π' g (A v)) (ht : IsTraceClass (repOp π μ f)) :
    IsTraceClass (repOp π' μ f) ∧ repTrace π' μ f = repTrace π μ f := by
  have h : repOp π' μ f = (A : H →L[ℂ] K) ∘L repOp π μ f ∘L (A.symm : K →L[ℂ] H) := by
    rw [← comp_assoc, hπ.comp_repOp hπ' hf hc (A : H →L[ℂ] K) hA]
    ext v; simp
  rw [repTrace, h]
  exact ⟨ht.comp_comp _ _, ht.trace_conj A⟩
end IsUnitaryRep
end GlobalTheory.OpTrace
