-- Prove2me | solution 1 for GlobalTheory.OpTrace.trace_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:16:12.204902+00:00
-- url     : https://prove2.me/submissions/d2e3f648-803f-4773-b35e-9bfea3769b34

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
variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}
namespace GlobalTheory.OpTrace
theorem _root_.solution {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : trace (B ∘L C) = trace (C ∘L B) := by
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  exact h3.tsum_eq.trans h4.tsum_eq.symm
end GlobalTheory.OpTrace
