-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_complexUnits_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:52:58.923801+00:00
-- url     : https://prove2.me/submissions/7a8318f6-8d25-43e3-98ae-ef33a0fdbc8d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_re_eq_zero_of_norm_exp_one_cpow
import Theorems.Thm_GroundTheory_Global_existsUnique_prod_mul_I_of_re_eq_zero
import Theorems.Thm_GroundTheory_Global_existsUnique_complexUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (χ : ℂˣ →ₜ* Circle) :
    ∃! p : ℤ × ℝ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : ℤ × ℂ => ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2)
    (existsUnique_complexUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos 1).ne'
  have h := hp (Units.mk0 _ hne)
  rw [Units.val_mk0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos 1),
    div_self hne, one_zpow, one_mul] at h
  rw [← h, Circle.norm_coe]
end GroundTheory.Global
