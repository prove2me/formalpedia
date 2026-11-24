-- Prove2me | solution 1 for GlobalTheory.SchwartzIntegral.weightedDerivCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:57.223552+00:00
-- url     : https://prove2.me/submissions/17bd00b1-2bb4-4de9-95bf-09a2581c4f80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFunctionalIntegralComm

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
namespace GlobalTheory.SchwartzIntegral
theorem _root_.solution (k m : ℕ) (f : 𝓢(E, ℂ)) : weightedDerivCLM k m f = weightedDeriv k m f := rfl
end GlobalTheory.SchwartzIntegral
