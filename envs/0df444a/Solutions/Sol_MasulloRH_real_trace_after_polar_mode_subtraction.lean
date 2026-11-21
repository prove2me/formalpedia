-- Prove2me | solution 1 for MasulloRH.real_trace_after_polar_mode_subtraction
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:19:53.500306+00:00
-- url     : https://prove2.me/submissions/befebd9e-af91-457a-b378-eb7914eedc0d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set

private theorem modal_scalar (A B z : ℝ) (hz : z < 1) :
    A*(B/(1-z))-A*B = A*B*z*(1-z)⁻¹ := by
  rw [← div_eq_mul_inv]
  field_simp [ne_of_gt (sub_pos.mpr hz)]
  ring

theorem solution (a b : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : IntegrableOn f (Icc a b)) :
    let μ := volume.restrict (Icc a b)
    let h (j : ℕ) (x : ℝ) := f x * Real.exp (-x/2) * Real.exp (-2*x)^(j+1)
    Summable (fun j => ∫ x, |h j x| ∂μ) ∧
      HasSum (fun j => ∫ x, h j x ∂μ)
        ((∫ x, f x * (Real.exp (-x/2) / (1-Real.exp (-2*x))) ∂μ) -
         ∫ x, f x * Real.exp (-x/2) ∂μ) := by
  intro μ h
  let q := Real.exp (-2*a)
  have hq : 0 < q := Real.exp_pos _
  have hlt : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hm : ∀ᵐ x ∂μ, x ∈ Icc a b := ae_restrict_mem measurableSet_Icc
  have hfi : Integrable f μ := hf
  have hx (x : ℝ) (hx : x ∈ Icc a b) :
      Real.exp (-x/2) ≤ 1 ∧ Real.exp (-2*x) ≤ q := by
    have := hx.1
    exact ⟨Real.exp_le_one_iff.mpr (by linarith),Real.exp_le_exp.mpr (by linarith)⟩
  have hh (j : ℕ) : AEStronglyMeasurable (h j) μ :=
    (hfi.aestronglyMeasurable.mul (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x/2))).aestronglyMeasurable).mul
      (by fun_prop : Continuous (fun x : ℝ => Real.exp (-2*x)^(j+1))).aestronglyMeasurable
  have hb (j : ℕ) : ∀ᵐ x ∂μ, ‖h j x‖ ≤ |f x| *q^j := by
    filter_upwards [hm] with x hmem
    simp only [h, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (pow_pos (Real.exp_pos _) _)]
    calc
      |f x| *Real.exp (-x/2)*Real.exp (-2*x)^(j+1) ≤
          (|f x| *1)*q^(j+1) := mul_le_mul
             (mul_le_mul_of_nonneg_left (hx _ hmem).1 (abs_nonneg _))
             (pow_le_pow_left₀ (Real.exp_pos _).le (hx _ hmem).2 _) (by positivity) (by positivity)
      _ ≤ |f x| *q^j := by rw [mul_one, pow_succ]; nlinarith [mul_nonneg (abs_nonneg (f x)) (mul_nonneg (pow_nonneg hq.le j) (sub_nonneg.mpr hlt.le))]
  have hi j : Integrable (h j) μ := (hfi.abs.mul_const _).mono' (hh j) (hb j)
  have hsum : Summable (fun j => ∫ x, |h j x| ∂μ) := by
    have hg := (summable_geometric_of_lt_one hq.le hlt).mul_left (∫ x, |f x| ∂μ)
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hg
    intro j
    rw [← integral_mul_const]
    exact integral_mono_ae (hi j).abs (hfi.abs.mul_const _) (by filter_upwards [hb j] with x hxj; simpa only [Real.norm_eq_abs] using hxj)
  have ht (x : ℝ) (hx' : x ∈ Icc a b) :
      HasSum (fun j => h j x)
        (f x * (Real.exp (-x/2)/(1-Real.exp (-2*x))) - f x*Real.exp (-x/2)) := by
    have hr : Real.exp (-2*x)<1 := lt_of_le_of_lt (hx x hx').2 hlt
    have hs := (hasSum_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (f x * Real.exp (-x/2)*Real.exp (-2*x))
    have he : (fun j : ℕ => h j x) = (fun j => (f x * Real.exp (-x/2)*Real.exp (-2*x)) * Real.exp (-2*x)^j) := by
      funext j; dsimp [h]; rw [pow_succ]; ring
    rw [he]
    rw [modal_scalar _ _ _ hr]
    exact hs
  refine ⟨hsum, ?_⟩
  have hn : Summable (fun j => ∫ x, ‖h j x‖ ∂μ) := by simpa only [Real.norm_eq_abs] using hsum
  have hs := (hasSum_integral_of_summable_integral_norm hi hn)
  have hbase : Integrable (fun x => f x * Real.exp (-x/2)) μ :=
    hfi.abs.mono' (hfi.aestronglyMeasurable.mul (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x/2))).aestronglyMeasurable) (by
      filter_upwards [hm] with x hmem
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hx _ hmem).1)
  have hre : (fun x => (∑' j, h j x) + f x * Real.exp (-x/2)) =ᵐ[μ]
       (fun x => f x*(Real.exp (-x/2)/(1-Real.exp (-2*x)))) := by
    filter_upwards [hm] with x hx'
    rw [(ht x hx').tsum_eq]; ring
  have hden : Integrable (fun x => f x*(Real.exp (-x/2)/(1-Real.exp (-2*x)))) μ := by
    apply (hfi.abs.mul_const ((1-q)⁻¹)).mono'
    · exact hfi.aestronglyMeasurable.mul (by fun_prop : Measurable (fun x : ℝ => Real.exp (-x/2)/(1-Real.exp (-2*x)))).aestronglyMeasurable
    filter_upwards [hm] with x hx'
    have hpos := sub_pos.mpr (lt_of_le_of_lt (hx _ hx').2 hlt)
    simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (Real.exp_pos _),abs_of_pos hpos]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [← one_div]
    exact div_le_div₀ (by positivity) (hx _ hx').1 (sub_pos.mpr hlt) (by linarith [(hx _ hx').2])
  have hti : Integrable (fun x => ∑' j, h j x) μ := (hden.sub hbase).congr (by
    filter_upwards [hm] with x hx'
    exact (ht x hx').tsum_eq.symm)
  rw [← integral_congr_ae hre,integral_add hti hbase,add_sub_cancel_right]
  exact hs
