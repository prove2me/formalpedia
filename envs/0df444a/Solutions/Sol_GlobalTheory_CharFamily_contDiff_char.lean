-- Prove2me | solution 1 for GlobalTheory.CharFamily.contDiff_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:47.880737+00:00
-- url     : https://prove2.me/submissions/1dd672ea-a0ab-49ce-9a47-7a7cbd24d490

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CharFamily
theorem _root_.solution (L : E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => Complex.exp (I * (L x : ℂ))) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (I * (y : ℂ))) := by fun_prop
  exact hc.comp L.contDiff
end GlobalTheory.CharFamily
