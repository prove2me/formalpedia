-- Prove2me | solution 1 for GlobalTheory.T.schwartz_seminorm_translate_sub_lineDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:35.514443+00:00
-- url     : https://prove2.me/submissions/ded15865-d2f8-4b6a-a05d-6164a4896a20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLeStatement
import Theorems.Thm_GlobalTheory_SchwartzTranslate_seminorm_translate_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | exact GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le | (intros; apply GlobalTheory.SchwartzTranslate.seminorm_translate_sub_le <;> assumption)
end _root_.GlobalTheory.T
