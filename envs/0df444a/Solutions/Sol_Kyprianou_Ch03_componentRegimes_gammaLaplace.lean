-- Prove2me | solution 1 for Kyprianou.Ch03.componentRegimes_gammaLaplace
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:10:04.47121+00:00
-- url     : https://prove2.me/submissions/f2f85a64-d640-4059-a463-216db20cdef2

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace GLAux

open Set

lemma inner_s (c gamma q x : ℝ) (hx : 0 < x) (hq : 0 ≤ q) :
    ∫ s in Ioc 0 q, c * Real.exp (-(gamma + s) * x) =
      c * Real.exp (-gamma * x) / x * (1 - Real.exp (-q * x)) := by
  rw [← intervalIntegral.integral_of_le hq]
  have hd : ∀ s ∈ uIcc 0 q, HasDerivAt (fun s => -c * Real.exp (-(gamma + s) * x) / x)
      (c * Real.exp (-(gamma + s) * x)) s := by
    intro s _
    have hx0 : x ≠ 0 := hx.ne'
    have h1 : HasDerivAt (fun s => -(gamma + s) * x) (-x) s := by
      have := ((hasDerivAt_id s).const_add gamma).neg.mul_const x
      simpa using this
    have h2 := (h1.exp.const_mul (-c)).div_const x
    have e : c * Real.exp (-(gamma + s) * x) = -c * (Real.exp (-(gamma + s) * x) * -x) / x := by
      field_simp
    rw [e]; exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : -(gamma + q) * x = -gamma * x + -q * x := by ring
  rw [e1, Real.exp_add]
  simp only [add_zero]
  field_simp
  ring

lemma inner_x (c gamma s : ℝ) (hs : 0 < gamma + s) :
    ∫ x in Ioi 0, c * Real.exp (-(gamma + s) * x) = c / (gamma + s) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
  simp
  have e : -s + -gamma = -(gamma + s) := by ring
  rw [e]
  field_simp

lemma outer (c gamma q : ℝ) (hg : 0 < gamma) (hq : 0 ≤ q) :
    ∫ s in Ioc 0 q, c / (gamma + s) = c * Real.log (1 + q / gamma) := by
  rw [← intervalIntegral.integral_of_le hq]
  have : (fun s => c / (gamma + s)) = fun s => c * (s + gamma)⁻¹ := by
    funext s; rw [add_comm]; ring
  rw [this, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right (fun s => s⁻¹) gamma,
    integral_inv_of_pos (by linarith) (by linarith)]
  congr 2
  field_simp
  ring

lemma swap (c gamma q : ℝ) (hc : 0 < c) (hg : 0 < gamma) (hq : 0 ≤ q) :
    ∫ x in Ioi 0, ∫ s in Ioc 0 q, c * Real.exp (-(gamma + s) * x) =
      ∫ s in Ioc 0 q, ∫ x in Ioi 0, c * Real.exp (-(gamma + s) * x) := by
  apply integral_integral_swap
  have hbnd : Integrable (fun p : ℝ × ℝ => (c * Real.exp (-gamma * p.1)) * (1 : ℝ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc 0 q))) := by
    exact Integrable.mul_prod (f := fun x => c * Real.exp (-gamma * x)) (g := fun _ => (1:ℝ))
      ((integrableOn_exp_mul_Ioi (by linarith : -gamma < 0) 0).const_mul c)
      (integrable_const 1)
  refine hbnd.mono' (by apply Continuous.aestronglyMeasurable; fun_prop) ?_
  rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)]
  refine Eventually.of_forall fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := hp
  simp only [mem_Ioi, mem_Ioc] at hp1 hp2
  show ‖c * Real.exp (-(gamma + p.2) * p.1)‖ ≤ c * Real.exp (-gamma * p.1) * 1
  rw [mul_one, Real.norm_eq_abs, abs_of_pos (mul_pos hc (Real.exp_pos _))]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply Real.exp_le_exp.2
  nlinarith

end GLAux

open Set in
theorem solution
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ q : ℝ, 0 ≤ q →
      (∫ x in Set.Ioi (0 : ℝ),
        (1 - Real.exp (-q * x)) ∂
          (Kyprianou.Ch03.temperedStablePositiveMeasure c 0 gamma)) =
        c * Real.log (1 + q / gamma)) := by
  intro q hq
  unfold Kyprianou.Ch03.temperedStablePositiveMeasure
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (if 0 < x
      then c * Real.exp (-gamma * x) / (x ^ (1 + (0:ℝ))) else 0)) := by
    apply Measurable.ennreal_ofReal
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Ioi]
  rw [← GLAux.outer c gamma q hgamma hq]
  have h2 : ∫ s in Ioc 0 q, c / (gamma + s) =
      ∫ s in Ioc 0 q, ∫ x in Ioi 0, c * Real.exp (-(gamma + s) * x) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact (GLAux.inner_x c gamma s (by linarith [hs.1])).symm
  rw [h2, ← GLAux.swap c gamma q hc hgamma hq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [mem_Ioi] at hx
  dsimp only
  rw [GLAux.inner_s c gamma q x hx hq]
  simp only [hx, if_true, add_zero, Real.rpow_one, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
