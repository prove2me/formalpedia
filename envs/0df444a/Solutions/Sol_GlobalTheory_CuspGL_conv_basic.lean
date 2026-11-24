-- Prove2me | solution 1 for GlobalTheory.CuspGL.conv_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:06.770684+00:00
-- url     : https://prove2.me/submissions/70fb0118-4983-4a62-93ed-005b49352240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
import Theorems.Thm_GlobalTheory_CuspGL_conv_comm
import Theorems.Thm_GlobalTheory_CuspGL_conv_assoc
import Theorems.Thm_GlobalTheory_CuspGL_conv_add_left
import Theorems.Thm_GlobalTheory_CuspGL_conv_sub_left

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
theorem _root_.solution : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P :=
  fun _ _ P _ => ⟨finite_monic_factorisations P, fun a b c =>
    ⟨conv_comm a b P, conv_assoc a b c P, conv_add_left a b c P, conv_sub_left a b c P⟩⟩
end GlobalTheory.CuspGL
