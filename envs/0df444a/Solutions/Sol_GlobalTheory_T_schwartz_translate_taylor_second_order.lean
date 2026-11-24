-- Prove2me | solution 1 for GlobalTheory.T.schwartz_translate_taylor_second_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:22.812309+00:00
-- url     : https://prove2.me/submissions/af2331ea-e9ae-4886-aeb2-65073da15736

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrderStatement
import Theorems.Thm_GlobalTheory_SchwartzTranslateUnif_seminorm_translate_sub_lineDeriv_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | exact GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | (intros; apply GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le <;> assumption)
end _root_.GlobalTheory.T
