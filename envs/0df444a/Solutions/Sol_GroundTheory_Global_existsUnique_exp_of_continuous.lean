-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_exp_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:27.115466+00:00
-- url     : https://prove2.me/submissions/bfca86b7-916b-441c-b251-bced18be1073

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Theorems.Thm_GroundTheory_Global_existsUnique_circleExp_of_continuous
import Theorems.Thm_GroundTheory_Global_eq_of_forall_exp_mul_eq

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
theorem _root_.solution (χ : ℝ → ℂˣ) (hχ : Continuous χ)
    (hmul : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃! s : ℂ, ∀ t : ℝ, (χ t : ℂ) = Complex.exp (s * t) := by
  refine existsUnique_of_exists_of_unique ?_
    (fun s s' hs hs' => eq_of_forall_exp_mul_eq fun t => by rw [← hs, ← hs'])
  have hc : Continuous fun t => (χ t : ℂ) := Units.continuous_val.comp hχ
  have hnpos : ∀ t, 0 < ‖(χ t : ℂ)‖ := fun t => norm_pos_iff.mpr (χ t).ne_zero

  have ℓadd : ∀ s t, Real.log ‖(χ (s + t) : ℂ)‖ =
      Real.log ‖(χ s : ℂ)‖ + Real.log ‖(χ t : ℂ)‖ := by
    intro s t
    rw [hmul, Units.val_mul, norm_mul]
    exact Real.log_mul (hnpos s).ne' (hnpos t).ne'
  have ℓcont : Continuous fun t => Real.log ‖(χ t : ℂ)‖ := hc.norm.log fun t => (hnpos t).ne'
  have ℓlin : ∀ t, Real.log ‖(χ t : ℂ)‖ = Real.log ‖(χ 1 : ℂ)‖ * t := by
    intro t
    have := map_real_smul (AddMonoidHom.mk' (fun t => Real.log ‖(χ t : ℂ)‖) ℓadd) ℓcont t 1
    simpa [mul_comm] using this

  let u : ℝ → Circle := fun t => ⟨(χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ),
    mem_sphere_zero_iff_norm.2 (by simp [(hnpos t).ne'])⟩
  have ucont : Continuous u := by
    apply Continuous.subtype_mk
    exact hc.div (Complex.continuous_ofReal.comp hc.norm) fun t => by
      exact_mod_cast (hnpos t).ne'
  have umul : ∀ s t, u (s + t) = u s * u t := by
    intro s t
    apply Circle.coe_injective
    rw [Circle.coe_mul]
    show (χ (s + t) : ℂ) / (‖(χ (s + t) : ℂ)‖ : ℂ) =
      (χ s : ℂ) / (‖(χ s : ℂ)‖ : ℂ) * ((χ t : ℂ) / (‖(χ t : ℂ)‖ : ℂ))
    rw [hmul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  obtain ⟨τ, hτ, -⟩ := existsUnique_circleExp_of_continuous u ucont umul
  refine ⟨Real.log ‖(χ 1 : ℂ)‖ + τ * I, fun t => ?_⟩
  have h1 : (χ t : ℂ) = (‖(χ t : ℂ)‖ : ℂ) * (u t : ℂ) := by
    show _ = _ * (_ / _)
    rw [mul_div_cancel₀]
    exact_mod_cast (hnpos t).ne'
  have h2 : (‖(χ t : ℂ)‖ : ℂ) = Complex.exp ((Real.log ‖(χ 1 : ℂ)‖ * t : ℝ)) := by
    rw [← ℓlin, ← Complex.ofReal_exp, Real.exp_log (hnpos t)]
  rw [h1, h2, hτ t, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end GroundTheory.Global
