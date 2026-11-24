-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:52.010852+00:00
-- url     : https://prove2.me/submissions/ca09bea8-ef85-4e5e-b80f-9a92120f2a25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Theorems.Thm_GlobalTheory_CuspGL_conv_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution (a b c : F[X] → ℂ) (P : F[X]) :
    conv (a - b) c P = conv a c P - conv b c P := by
  simp only [conv_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
end GlobalTheory.CuspGL
