-- Prove2me | solution 1 for GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:19.902885+00:00
-- url     : https://prove2.me/submissions/7431e40c-613e-4b71-a6d5-f0f93b739eb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Theorems.Thm_GlobalTheory_isOfFinOrder_of_isOfFinOrder_mapRingHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 → (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B, IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  first | exact @GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | exact GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | (intros; apply GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom <;> assumption)
end _root_.GlobalTheory.T
