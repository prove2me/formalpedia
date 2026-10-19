-- Prove2me | solution 1 for OAI.UniformSparsestCut.GaussianPoincare.rotation_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:47:12.622223+00:00
-- url     : https://prove2.me/submissions/7ab58e87-98d5-4664-b0f4-1fef9b2fad33

import Mathlib
import Definitions.Def_OAIQWUS000

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianPoincare
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local notation "μ" => stdGaussian E

lemma gaussian_dual_sq (L : StrongDual ℝ E) : ∫ x, (L x)^2 ∂μ = ‖L‖^2 := by
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa only [sub_zero] using h

lemma gaussian_dual_abs (L : StrongDual ℝ E) : ∫ x, |L x| ∂μ ≤ ‖L‖ := by
  by_cases hz : L = 0
  · simp [hz]
  have h0 : 0 < ‖L‖ := norm_pos_iff.mpr hz
  have hL : MemLp (fun x => L x) 2 μ := IsGaussian.memLp_dual _ _ _ (by norm_num)
  have hi : Integrable (fun x => (|L x|-‖L‖)^2) μ := by
    simpa using (hL.norm.sub (memLp_const ‖L‖)).integrable_sq
  have hn : 0 ≤ ∫ x, (|L x|-‖L‖)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have he : (∫ x, (|L x|-‖L‖)^2 ∂μ) = 2*‖L‖^2-2*‖L‖*(∫ x, |L x| ∂μ) := by
    simp_rw [sub_sq, sq_abs]
    have hc := ((hL.integrable (by norm_num)).abs.const_mul 2).mul_const ‖L‖
    rw [integral_add (f := fun x => L x^2-2*|L x| *‖L‖)
      (g := fun _ => ‖L‖^2) (hL.integrable_sq.sub hc) (integrable_const _),
      integral_sub (f := fun x => L x^2) (g := fun x => 2*|L x| *‖L‖) hL.integrable_sq hc]
    rw [gaussian_dual_sq]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    rw [integral_mul_const, integral_const_mul]
    ring
  rw [he] at hn
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma path_hasDeriv (t : ℝ) (z : E × E) : HasDerivAt (fun u => path u z) (tangent t z) t := by
  exact ((Real.hasDerivAt_cos t).smul_const z.1).add ((Real.hasDerivAt_sin t).smul_const z.2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tangent_norm_le (t : ℝ) (z : E × E) : ‖tangent t z‖ ≤ ‖z.1‖ + ‖z.2‖ := by
  calc
    _ ≤ ‖-Real.sin t • z.1‖ + ‖Real.cos t • z.2‖ := norm_add_le _ _
    _ = |Real.sin t| *‖z.1‖ + |Real.cos t| *‖z.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1*‖z.1‖ + 1*‖z.2‖ := add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _))
    _ = _ := by ring

lemma integral_rotation (f : E × E → ℝ) (hf : AEStronglyMeasurable f ((μ).prod μ)) (t : ℝ) :
    ∫ z, f (path t z, tangent t z) ∂((μ).prod μ) = ∫ z, f z ∂((μ).prod μ) := by
  have hr := IsGaussian.map_rotation_eq_self (integral_id_stdGaussian (E := E)) t
  have hm : AEMeasurable (ContinuousLinearMap.rotation (E := E) t) ((μ).prod μ) := by fun_prop
  have h := integral_map hm (hr ▸ hf)
  exact h.symm.trans (congrArg (fun ν => ∫ z, f z ∂ν) hr)

lemma derivative_integrable (h : E → ℝ) (hh : ContDiff ℝ 1 h) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, ‖fderiv ℝ h x‖ ≤ M) :
    Integrable (fun z : E × E => |fderiv ℝ h z.1 z.2|) ((μ).prod μ) := by
  have hi : Integrable (fun z : E × E => M*‖z.2‖) ((μ).prod μ) :=
    ((IsGaussian.integrable_id («μ» := μ)).norm.comp_snd μ).const_mul M
  apply hi.mono' (by have hc := hh.continuous_fderiv (by norm_num); fun_prop)
  filter_upwards with z
  simp only [Real.norm_eq_abs, abs_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))

lemma derivative_average_bound (h : E → ℝ) (hh : ContDiff ℝ 1 h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖fderiv ℝ h x‖ ≤ M) :
    (∫ z : E × E, |fderiv ℝ h z.1 z.2| ∂((μ).prod μ)) ≤ ∫ x, ‖fderiv ℝ h x‖ ∂μ := by
  rw [integral_prod _ (derivative_integrable h hh hM hb)]
  refine integral_mono_ae (derivative_integrable h hh hM hb).integral_prod_left ?_ ?_
  · exact (integrable_const M).mono' (by have hc := hh.continuous_fderiv (by norm_num); fun_prop)
      (ae_of_all _ fun x => by simpa using hb x)
  · filter_upwards with x using gaussian_dual_abs (fderiv ℝ h x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma endpoint_bound (h : E → ℝ) (hh : ContDiff ℝ 1 h) (z : E × E) :
    |h z.1-h z.2| ≤ ∫ t in (0 : ℝ)..(Real.pi/2),
      |fderiv ℝ h (path t z) (tangent t z)| := by
  have hd (t : ℝ) : HasDerivAt (fun t => h (path t z))
      (fderiv ℝ h (path t z) (tangent t z)) t :=
    ((hh.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t (path_hasDeriv t z)
  have hc : Continuous (fun t => fderiv ℝ h (path t z) (tangent t z)) := by
    have hD := hh.continuous_fderiv (by norm_num)
    unfold path tangent
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 (Real.pi/2))
  have hn := intervalIntegral.abs_integral_le_integral_abs («μ» := volume)
    (f := fun t => fderiv ℝ h (path t z) (tangent t z))
    (by positivity : (0 : ℝ) ≤ Real.pi/2)
  rw [he] at hn
  simpa [path, abs_sub_comm] using hn

lemma rotation_first_moment_oai (h : E → ℝ) (hh : ContDiff ℝ 1 h)
    {M B : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖fderiv ℝ h x‖ ≤ M)
    (hB : ∀ x, ‖h x‖ ≤ B) :
    (∫ z : E × E, |h z.1-h z.2| ∂((μ).prod μ)) ≤
      (Real.pi/2) * ∫ x, ‖fderiv ℝ h x‖ ∂μ := by
  let b : ℝ := Real.pi/2
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  let ν := volume.restrict (Ioc (0 : ℝ) b)
  have : IsFiniteMeasure ν := by dsimp [ν]; infer_instance
  let g (t : ℝ) (z : E × E) := |fderiv ℝ h (path t z) (tangent t z)|
  have hc : Continuous (Function.uncurry g) := by
    have hD := hh.continuous_fderiv (by norm_num)
    dsimp [g, Function.uncurry, path, tangent]
    fun_prop
  have hnorm : Integrable (fun z : E × E => ‖z.1‖+‖z.2‖) ((μ).prod μ) :=
    ((IsGaussian.integrable_id («μ» := stdGaussian E)).norm.comp_fst _).add
      ((IsGaussian.integrable_id («μ» := stdGaussian E)).norm.comp_snd _)
  have hI : Integrable (Function.uncurry g) (ν.prod ((μ).prod μ)) := by
    apply ((hnorm.const_mul M).comp_snd ν).mono' hc.aestronglyMeasurable
    filter_upwards with x
    dsimp [g, Function.uncurry]
    simp only [ abs_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (tangent_norm_le _ _) hM))
  have hInt : Integrable (fun z => ∫ t in (0 : ℝ)..b, g t z) ((μ).prod μ) := by
    simpa only [intervalIntegral.integral_of_le hb0, ν, Function.uncurry_apply_pair] using hI.integral_prod_right
  have hLeft : Integrable (fun z : E × E => |h z.1-h z.2|) ((μ).prod μ) := by
    apply (integrable_const (2*B)).mono' (by fun_prop)
    filter_upwards with z
    simpa only [Real.norm_eq_abs, abs_abs] using
      (norm_sub_le (h z.1) (h z.2)).trans (by linarith [hB z.1,hB z.2])
  have hrotate (t : ℝ) : (∫ z, g t z ∂((μ).prod μ)) =
      ∫ z : E × E, |fderiv ℝ h z.1 z.2| ∂((μ).prod μ) := by
    exact integral_rotation _ (derivative_integrable h hh hM hb).aestronglyMeasurable t
  calc
    _ ≤ ∫ z : E × E, (∫ t in (0 : ℝ)..b, g t z) ∂((μ).prod μ) :=
      integral_mono hLeft hInt (endpoint_bound h hh)
    _ = ∫ t in (0 : ℝ)..b, ∫ z, g t z ∂((μ).prod μ) := by
      symm
      apply intervalIntegral_integral_swap
      simpa only [uIoc_of_le hb0] using hI
    _ = b * ∫ z : E × E, |fderiv ℝ h z.1 z.2| ∂((μ).prod μ) := by
      simp_rw [hrotate]
      simp [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (derivative_average_bound h hh hM hb) hb0

end UniformSparsestCut.GaussianPoincare

end

end OAI
end

theorem solution.{u1} : type_of% @OAI.UniformSparsestCut.GaussianPoincare.rotation_first_moment_oai.{u1} := @OAI.UniformSparsestCut.GaussianPoincare.rotation_first_moment_oai.{u1}
