-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegral.seminorm_le_norm_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:25.983426+00:00
-- url     : https://prove2.me/submissions/816cf1c8-4aa3-46b6-b3be-e653238b4ca6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm
import Theorems.Thm_GlobalTheory_SchwartzIntegral_seminorm_le_norm_weightedDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.SchwartzIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] {ν : Measure W}
namespace GlobalTheory.SchwartzIntegral
theorem _root_.solution (s : Finset (ℕ × ℕ)) (f : 𝓢(E, ℂ)) {i : ℕ × ℕ} (hi : i ∈ s) :
    SchwartzMap.seminorm ℂ i.1 i.2 f ≤ ‖embed s f‖ :=
  (seminorm_le_norm_weightedDeriv _ _ f).trans (norm_le_pi_norm (embed s f) ⟨i, hi⟩)
end GlobalTheory.SchwartzIntegral
