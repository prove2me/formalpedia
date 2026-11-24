-- Prove2me | solution 1 for GlobalTheory.CocycleChar.pow_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:33.655965+00:00
-- url     : https://prove2.me/submissions/ab57faa6-093a-4e27-8ce2-be62d04e12fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousCharacterCocycleTrivialNearZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CocycleChar
namespace GlobalTheory.CocycleChar
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)
end GlobalTheory.CocycleChar
