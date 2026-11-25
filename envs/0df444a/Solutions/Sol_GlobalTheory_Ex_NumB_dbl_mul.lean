-- Prove2me | solution 1 for GlobalTheory.Ex.NumB.dbl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:04.465825+00:00
-- url     : https://prove2.me/submissions/18bb6d64-dfca-42d5-84ba-e4500905c5af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_GlobalTheory_Ex_cub_rot
import Theorems.Thm_P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)
namespace GlobalTheory.Ex.NumB
theorem _root_.solution (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by
  have c := B.cub.coc x y (x * y)⁻¹ (x * y)
  have d := B.cub.coc y y⁻¹ x⁻¹ (x * y)
  rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y] at c
  rw [mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹] at d
  have a := B.cub.compat x x⁻¹ x y
  have b := B.cub.compat y y⁻¹ x y
  rw [mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y] at a
  rw [mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x] at b
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have c := E c; have d := E d; have s := E (B.σ_mul_symm x y)
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢
  linear_combination (norm := abel) c - d - a - b - s
end GlobalTheory.Ex.NumB
