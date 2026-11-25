-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_realUnits_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:07.142713+00:00
-- url     : https://prove2.me/submissions/c50b569a-d254-44a8-99b9-c7c6970b5063

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Theorems.Thm_GroundTheory_Global_re_eq_zero_of_norm_exp_one_cpow
import Theorems.Thm_GroundTheory_Global_existsUnique_prod_mul_I_of_re_eq_zero
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_existsUnique_realUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_circleToUnits



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (χ : ℝˣ →ₜ* Circle) :
    ∃! p : Fin 2 × ℝ, ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  apply existsUnique_prod_mul_I_of_re_eq_zero (P := fun p : Fin 2 × ℂ => ∀ x : ℝˣ,
      (χ x : ℂ) = (Real.sign (x : ℝ) : ℂ) ^ (p.1 : ℕ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ p.2)
    (existsUnique_realUnits (circleToUnits.comp χ))
  intro p hp
  apply re_eq_zero_of_norm_exp_one_cpow
  have h := hp (Units.mk0 (Real.exp 1) (Real.exp_pos 1).ne')
  simp only [Units.val_mk0, Real.sign_of_pos (Real.exp_pos 1), abs_of_pos (Real.exp_pos 1),
    Complex.ofReal_one, one_pow, one_mul] at h
  rw [← h, Circle.norm_coe]
end GroundTheory.Global
