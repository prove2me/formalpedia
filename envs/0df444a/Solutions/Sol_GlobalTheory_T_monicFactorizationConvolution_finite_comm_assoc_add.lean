-- Prove2me | solution 1 for GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:11.835796+00:00
-- url     : https://prove2.me/submissions/cf47f991-7e47-4d30-9b97-bf972a66e370

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Theorems.Thm_GlobalTheory_CuspGL_conv_basic


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
theorem _root_.solution : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P := by
  first | exact @GlobalTheory.CuspGL.conv_basic | exact GlobalTheory.CuspGL.conv_basic | (intros; apply GlobalTheory.CuspGL.conv_basic <;> assumption)
end _root_.GlobalTheory.T
