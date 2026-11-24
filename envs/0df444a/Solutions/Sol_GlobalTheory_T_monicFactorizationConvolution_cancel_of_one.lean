-- Prove2me | solution 1 for GlobalTheory.T.monicFactorizationConvolution_cancel_of_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:43.933243+00:00
-- url     : https://prove2.me/submissions/cf8935a1-3d79-4415-ad09-eae349c7bff2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionCancelOfOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionCancelOfOneStatement
import Theorems.Thm_GlobalTheory_CuspGL_ConvCancel_conv_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 → (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  first | exact @GlobalTheory.CuspGL.ConvCancel.conv_cancel | exact GlobalTheory.CuspGL.ConvCancel.conv_cancel | (intros; apply GlobalTheory.CuspGL.ConvCancel.conv_cancel <;> assumption)
end _root_.GlobalTheory.T
