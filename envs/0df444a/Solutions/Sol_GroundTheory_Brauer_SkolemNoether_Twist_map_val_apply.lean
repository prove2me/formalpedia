-- Prove2me | solution 1 for GroundTheory.Brauer.SkolemNoether.Twist.map_val_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:59.805485+00:00
-- url     : https://prove2.me/submissions/10d80667-607b-4c95-9446-590b1ecd9e6d

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_bimoduleHom_tmul
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_smul
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
open GroundTheory.Brauer.SkolemNoether.Twist
variable (f : B →ₐ[K] A)
variable {f} {g : B →ₐ[K] A}
namespace GroundTheory.Brauer.SkolemNoether.Twist
theorem _root_.solution (φ : Twist f →ₗ[A ⊗[K] Bᵐᵒᵖ] Twist g) (b : B) :
    (φ (of f (f b))).val = (φ (of f 1)).val * g b := by
  have hb : of f (f b) = ((1 : A) ⊗ₜ[K] MulOpposite.op b) • of f 1 := by
    change f b = bimoduleHom f ((1 : A) ⊗ₜ[K] MulOpposite.op b) 1
    simp [bimoduleHom_tmul]
  rw [hb, map_smul, val_smul, bimoduleHom_tmul]
  simp
end GroundTheory.Brauer.SkolemNoether.Twist
