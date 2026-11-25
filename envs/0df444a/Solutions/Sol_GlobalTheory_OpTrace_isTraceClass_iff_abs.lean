-- Prove2me | solution 1 for GlobalTheory.OpTrace.isTraceClass_iff_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:02:32.57308+00:00
-- url     : https://prove2.me/submissions/1a3ee7fd-684b-412e-b5df-0f4d328e6e9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_IsTraceClass_comp_left

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
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
namespace GlobalTheory.OpTrace
theorem _root_.solution (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} :
    IsTraceClass T ↔ Summable fun i => ⟪e i, CFC.abs T (e i)⟫_ℂ := by
  have hn : ∀ x, ‖CFC.abs T x‖ = ‖T x‖ := norm_sqrt_apply T
  constructor
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).le
    rw [← hU]
    exact ((h.comp_left U).hasSum_trace e).summable
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).ge
    set A : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
    have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    have h2 : A ∘L A = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
    have hHS : IsHilbertSchmidt A := by
      rw [isHilbertSchmidt_iff e]
      refine h.norm.congr fun i => ?_
      rw [← h2, comp_apply, ← adjoint_inner_left, hA.adjoint_eq, inner_self_eq_norm_sq_to_K]
      simp
    rw [← hU, ← h2]
    exact (hHS.isTraceClass_comp hHS).comp_left U
end GlobalTheory.OpTrace
