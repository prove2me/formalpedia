-- Prove2me | solution 1 for GroundTheory.Brauer.exists_unit_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:33.103968+00:00
-- url     : https://prove2.me/submissions/f90c41a0-8be3-44ef-afca-5f95fb30be0c

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_nonempty_linearEquiv_of_finrank_eq
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_map_val
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_map_val_apply
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
open SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  [IsSimpleRing B] [FiniteDimensional K B]
namespace GroundTheory.Brauer
theorem _root_.solution (f g : B →ₐ[K] A) :
    ∃ a : Aˣ, ∀ x, g x = a * f x * ↑a⁻¹ := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq (K := K) (R := A ⊗[K] Bᵐᵒᵖ)
    (M := Twist f) (N := Twist g) (by rfl)
  set u := (e (Twist.of f 1)).val with hu
  set v := (e.symm (Twist.of g 1)).val with hv
  have hvu : v * u = 1 := by
    have := Twist.map_val e.toLinearMap v
    simp only [LinearEquiv.coe_coe, hv, Twist.of_val, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have huv : u * v = 1 := by
    have := Twist.map_val e.symm.toLinearMap u
    simp only [LinearEquiv.coe_coe, hu, Twist.of_val, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  refine ⟨⟨v, u, hvu, huv⟩, fun x ↦ ?_⟩
  have h := (Twist.map_val e.toLinearMap (f x)).symm.trans (Twist.map_val_apply e.toLinearMap x)
  simp only [LinearEquiv.coe_coe, ← hu] at h
  simp only [Units.val_mk, Units.inv_mk, mul_assoc, h, ← mul_assoc v u, hvu, one_mul]
end GroundTheory.Brauer
