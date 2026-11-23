-- Prove2me | solution 1 for GroundTheory.Brauer.SkolemNoether.bimoduleHom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:43.835677+00:00
-- url     : https://prove2.me/submissions/3dcb258f-acaf-45ef-ac26-a47f458b1330

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
namespace GroundTheory.Brauer.SkolemNoether
theorem _root_.solution (f : B →ₐ[K] A) (a : A) (b : Bᵐᵒᵖ) (x : A) :
    bimoduleHom f (a ⊗ₜ[K] b) x = a * x * f b.unop := by
  simp [bimoduleHom, mulRightHom, mul_assoc]
end GroundTheory.Brauer.SkolemNoether
