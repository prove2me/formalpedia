-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_complexUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:55.244024+00:00
-- url     : https://prove2.me/submissions/53e27eb4-0e97-4251-9528-54f77bef18f7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Theorems.Thm_GroundTheory_Global_ofReal_cpow_eq_exp
import Theorems.Thm_GroundTheory_Global_existsUnique_circle_zpow
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_eq_of_forall_exp_mul_eq
import Theorems.Thm_GroundTheory_Global_existsUnique_exp_of_continuous

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
theorem _root_.solution (χ : ℂˣ →ₜ* ℂˣ) :
    ∃! p : ℤ × ℂ, ∀ z : ℂˣ,
      (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ p.1 * ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ p.2 := by

  let e : ℝ → ℂˣ := fun t => Units.mk0 (Real.exp t : ℂ) (by exact_mod_cast (Real.exp_pos t).ne')
  have econt : Continuous e :=
    Units.isEmbedding_val₀.continuous_iff.mpr (Complex.continuous_ofReal.comp Real.continuous_exp)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Units.ext (by simp [e, Complex.exp_add]))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs

  obtain ⟨n, hn, hnu⟩ := existsUnique_circle_zpow (χ.comp circleToUnits)
  have hn' : ∀ w : Circle, (χ (circleToUnits w) : ℂ) = (w : ℂ) ^ n := hn
  have hnorm : ∀ z : ℂˣ, 0 < ‖(z : ℂ)‖ := fun z => norm_pos_iff.mpr z.ne_zero
  refine ⟨(n, s), fun z => ?_, ?_⟩
  · have hz : z = e (Real.log ‖(z : ℂ)‖) * circleToUnits (Circle.exp (Complex.arg z)) := by
      ext
      rw [Units.val_mul, coe_circleToUnits, Circle.coe_exp]
      show (z : ℂ) = (Real.exp (Real.log ‖(z : ℂ)‖) : ℂ) * _
      rw [Real.exp_log (hnorm z), Complex.norm_mul_exp_arg_mul_I]
    have hw : (Circle.exp (Complex.arg z) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
      rw [Circle.coe_exp, eq_div_iff (by exact_mod_cast (hnorm z).ne'), mul_comm,
        Complex.norm_mul_exp_arg_mul_I]
    conv_lhs => rw [hz]
    rw [map_mul, Units.val_mul, hs', hn', hw, ofReal_cpow_eq_exp (hnorm z), mul_comm]
  · rintro ⟨m, s'⟩ h'
    have hs's : s' = s := eq_of_forall_exp_mul_eq fun t => by
      have h1 := h' (e t)
      have he : ((e t : ℂˣ) : ℂ) = (Real.exp t : ℂ) := rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t),
        div_self (by exact_mod_cast (Real.exp_pos t).ne'), one_zpow, one_mul,
        ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
      rw [← h1, hs']
    have hmn : m = n := hnu m fun w => by
      have h1 := h' (circleToUnits w)
      rw [coe_circleToUnits, Circle.norm_coe] at h1
      simpa using h1
    simp [hmn, hs's]
end GroundTheory.Global
