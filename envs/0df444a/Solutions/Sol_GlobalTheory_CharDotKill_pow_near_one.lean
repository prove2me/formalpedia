-- Prove2me | solution 1 for GlobalTheory.CharDotKill.pow_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:08:38.675811+00:00
-- url     : https://prove2.me/submissions/ec1447b2-e6be-4d42-ad20-5c83cd2505e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact
import Theorems.Thm_GlobalTheory_KeyLemmaTwo_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CharDotKill
namespace GlobalTheory.CharDotKill
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)
end GlobalTheory.CharDotKill
