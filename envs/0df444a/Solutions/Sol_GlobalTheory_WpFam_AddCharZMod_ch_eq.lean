-- Prove2me | solution 1 for GlobalTheory.WpFam.AddCharZMod.ch_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:54.933697+00:00
-- url     : https://prove2.me/submissions/27d94604-710a-459d-8a20-bd7a740d7ed7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.AddCharZMod
namespace GlobalTheory.WpFam.AddCharZMod
theorem _root_.solution (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl
end GlobalTheory.WpFam.AddCharZMod
