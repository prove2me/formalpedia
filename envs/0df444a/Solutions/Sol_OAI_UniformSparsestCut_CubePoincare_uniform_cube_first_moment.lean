-- Prove2me | solution 1 for OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:47:11.386892+00:00
-- url     : https://prove2.me/submissions/9609744e-dfd2-43f4-ae55-546e6ea5325a

import Mathlib
import Definitions.Def_OAIQWUS000
import Theorems.Thm_OAI_UniformSparsestCut_GaussianPoincare_rotation_first_moment

section
-- module Solutions.OAIQW_UniformSparsestCut.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianCDF
local notation "μ" => gaussianReal 0 1

lemma φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos _ _ _ (by norm_num)
lemma φ_contDiff : ContDiff ℝ ∞ φ := by unfold φ gaussianPDFReal; fun_prop
lemma φ_integrable : Integrable φ := integrable_gaussianPDFReal _ _
lemma Φ_integral (x : ℝ) : Φ x = ∫ t in Iic x, φ t := by
  rw [Φ, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ (by norm_num)]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun t => gaussianPDFReal_nonneg (0:ℝ) 1 t))

lemma Φ_primitive (x : ℝ) : Φ x = Φ 0 + ∫ t in (0:ℝ)..x, φ t := by
  rw [Φ_integral, Φ_integral]
  have h := intervalIntegral.integral_Iic_sub_Iic
    (φ_integrable.integrableOn (s := Iic 0)) (φ_integrable.integrableOn (s := Iic x))
  linarith

lemma Φ_hasDeriv (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (φ_contDiff.continuous.intervalIntegrable (0:ℝ) x)
    φ_contDiff.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    φ_contDiff.continuous.continuousAt
  have h' := h.const_add (Φ 0)
  convert h' using 1 <;> first | rfl | exact funext Φ_primitive

lemma Φ_continuous : Continuous Φ := continuous_iff_continuousAt.mpr (fun x => (Φ_hasDeriv x).continuousAt)
lemma Φ_strictMono : StrictMono Φ := strictMono_of_deriv_pos (fun x => by rw [(Φ_hasDeriv x).deriv]; exact φ_pos x)
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := by
  constructor
  · exact (cdf_nonneg μ (x-1)).trans_lt (Φ_strictMono (by linarith))
  · exact (Φ_strictMono (show x < x+1 by linarith)).trans_le (cdf_le_one μ (x+1))

lemma Φ_surj {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) : ∃ x, Φ x = y := by
  apply intermediate_value_univ₂_eventually₂ (l₁ := atBot) (l₂ := atTop) Φ_continuous continuous_const
  · exact (tendsto_cdf_atBot μ).eventually (eventually_le_nhds hy.1)
  · exact (tendsto_cdf_atTop μ).eventually (eventually_ge_nhds hy.2)

lemma ψ_hasDeriv (x : ℝ) : HasDerivAt ψ (2*φ x) x := (Φ_hasDeriv x).const_mul 2 |>.sub_const 1
lemma ψ_mem (x : ℝ) : ψ x ∈ Ioo (-1:ℝ) 1 := by
  have h := Φ_mem x
  dsimp [ψ]; constructor <;> linarith [h.1,h.2]

lemma ψ_contDiff : ContDiff ℝ 1 ψ := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (ψ_hasDeriv x).differentiableAt
  · have he : deriv ψ = fun x => 2*φ x := funext (fun x => (ψ_hasDeriv x).deriv)
    rw [he]
    exact continuous_const.mul φ_contDiff.continuous

lemma ψ_deriv_bound (x : ℝ) : |2*φ x| ≤ 1 := by
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hge : 2 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  have he : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have he0 : 0 ≤ Real.exp (-x^2/2) := (Real.exp_pos _).le
  rw [abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (φ_pos x))]
  change 2*((Real.sqrt (2*Real.pi*1))⁻¹*Real.exp (-(x-0)^2/(2*1))) ≤ 1
  simp only [mul_one, sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹*(2*Real.exp (-x^2/2)) := by ring
    _ ≤ 1 := (inv_mul_le_iff₀ hs).mpr (by nlinarith)

lemma ψ_map : (μ).map ψ = uniform := by
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply ψ_contDiff.continuous.measurable measurableSet_Iic]
  change μ (ψ ⁻¹' Iic y) = (2:ℝ≥0∞)⁻¹ * (volume.restrict (Ioo (-1:ℝ) 1)) (Iic y)
  rw [Measure.restrict_apply measurableSet_Iic]
  by_cases h0 : y ≤ -1
  · have he : ψ ⁻¹' Iic y = ∅ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (h0.trans_lt (ψ_mem x).1)
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_empty_iff_false, iff_false]; grind
    simp [he,he']
  by_cases h1 : 1 ≤ y
  · have he : ψ ⁻¹' Iic y = univ := by
      ext x; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (ψ_mem x).2.le.trans h1
    have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioo (-1:ℝ) 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Ioo]; constructor <;> grind
    rw [he,he',measure_univ,Real.volume_Ioo]; norm_num;
    exact (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
  have hy : (y+1)/2 ∈ Ioo (0:ℝ) 1 := by constructor <;> linarith
  obtain ⟨x,hx⟩ := Φ_surj hy
  have he : ψ ⁻¹' Iic y = Iic x := by
    ext z
    simp only [mem_preimage, mem_Iic, ψ]
    rw [show y = 2*Φ x-1 by linarith]
    rw [show 2*Φ z-1 ≤ 2*Φ x-1 ↔ Φ z ≤ Φ x by constructor <;> intro hn <;> linarith]
    exact Φ_strictMono.le_iff_le
  have he' : Iic y ∩ Ioo (-1:ℝ) 1 = Ioc (-1:ℝ) y := by
    ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]; grind
  rw [he,he',← ofReal_cdf μ x,Real.volume_Ioc]
  change ENNReal.ofReal (Φ x) = (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal (y- -1)
  rw [hx,show y- -1 = y+1 by ring,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
  simp [div_eq_mul_inv,mul_comm]

instance uniform_probability : IsProbabilityMeasure uniform := by
  rw [← ψ_map]
  exact Measure.isProbabilityMeasure_map ψ_contDiff.continuous.measurable.aemeasurable

end UniformSparsestCut.GaussianCDF

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CubePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

instance cube_probability : IsProbabilityMeasure (cube (m := m)) := by
  unfold cube
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma Ψ_hasFDeriv (x : E) : HasFDerivAt Ψ (derivative x) x := by
  have hi (i : Fin m) := (GaussianCDF.ψ_hasDeriv (x i)).comp_hasFDerivAt x (coordinate i).hasFDerivAt
  have hp := hasFDerivAt_pi.mpr hi
  have h := (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp x hp
  convert h using 1 <;> rfl

lemma Ψ_contDiff : ContDiff ℝ 1 (Ψ (m := m)) := by
  have h : ContDiff ℝ 1 (fun x : E => fun i => GaussianCDF.ψ (x i)) :=
    contDiff_pi.mpr (fun i => GaussianCDF.ψ_contDiff.comp (coordinate i).contDiff)
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.contDiff.comp h

lemma Ψ_norm (x : E) : ‖Ψ x‖ ≤ Real.sqrt m := by
  have h : ‖Ψ x‖^2 ≤ (m:ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin m, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := GaussianCDF.ψ_mem (x i)
        change ‖GaussianCDF.ψ (x i)‖^2 ≤ 1
        rw [Real.norm_eq_abs, sq_abs]
        nlinarith [hi.1,hi.2]
      _ = _ := by simp
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m:ℝ), norm_nonneg (Ψ x)]

lemma derivative_norm (x : E) : ‖derivative x‖ ≤ 1 := by
  apply (derivative x).opNorm_le_bound (by norm_num)
  intro v
  simp only [one_mul]
  have h : ‖derivative x v‖^2 ≤ ‖v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change ‖2*GaussianCDF.φ (x i)*v i‖^2 ≤ ‖v i‖^2
    rw [norm_mul, mul_pow]
    have hi := GaussianCDF.ψ_deriv_bound (x i)
    have hh : ‖2*GaussianCDF.φ (x i)‖^2 ≤ 1 := by
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (2*GaussianCDF.φ (x i))]
    nlinarith [sq_nonneg ‖v i‖]
  nlinarith [norm_nonneg (derivative x v), norm_nonneg v]

lemma Ψ_map : (stdGaussian E).map Ψ = cube := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map Ψ_contDiff.continuous.measurable (by fun_prop)]
  have he : (Ψ (m := m)) ∘ WithLp.toLp 2 = WithLp.toLp 2 ∘
      (fun x : Fin m → ℝ => fun i => GaussianCDF.ψ (x i)) := rfl
  have hmeas : Measurable (fun x : Fin m → ℝ => fun i => GaussianCDF.ψ (x i)) :=
    Measurable.of_eval (fun i => GaussianCDF.ψ_contDiff.continuous.measurable.comp (measurable_pi_apply i))
  rw [he, ← Measure.map_map (by fun_prop) hmeas, Measure.pi_map_pi]
  · simp_rw [GaussianCDF.ψ_map]
    rfl
  · intro i
    exact GaussianCDF.ψ_contDiff.continuous.measurable.aemeasurable

lemma cube_first_moment_core (h : E → ℝ) (hh : ContDiff ℝ 1 h) :
    (∫ z : E × E, |h z.1-h z.2| ∂((cube (m := m)).prod cube)) ≤
      (Real.pi/2)*(∫ x : E, ‖fderiv ℝ h x‖ ∂cube) := by
  let μ := stdGaussian E
  let H : E → ℝ := h ∘ Ψ
  have hH : ContDiff ℝ 1 H := hh.comp Ψ_contDiff
  have hcompact := isCompact_closedBall (0:E) (Real.sqrt m)
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn hh.continuous.continuousOn
  obtain ⟨M,hM⟩ := hcompact.exists_bound_of_continuousOn (hh.continuous_fderiv (by norm_num)).continuousOn
  have hmem (x : E) : Ψ x ∈ Metric.closedBall 0 (Real.sqrt m) := by simpa using Ψ_norm x
  have hB' (x : E) : ‖H x‖ ≤ max B 0 := (hB _ (hmem x)).trans (le_max_left _ _)
  have hcomp (x : E) : fderiv ℝ H x = (fderiv ℝ h (Ψ x)).comp (derivative x) :=
    ((hh.differentiable (by norm_num) (Ψ x)).hasFDerivAt.comp x (Ψ_hasFDeriv x)).fderiv
  have hnorm (x : E) : ‖fderiv ℝ H x‖ ≤ ‖fderiv ℝ h (Ψ x)‖ := by
    rw [hcomp]
    exact ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
      ((mul_le_mul_of_nonneg_left (derivative_norm x) (norm_nonneg _)).trans_eq (mul_one _))
  have hdB (x : E) : ‖fderiv ℝ H x‖ ≤ max M 0 :=
    (hnorm x).trans ((hM _ (hmem x)).trans (le_max_left _ _))
  have hint : Integrable (fun x : E => ‖fderiv ℝ h (Ψ x)‖) μ := by
    apply (integrable_const (max M 0)).mono' ((hh.continuous_fderiv (by norm_num)).comp Ψ_contDiff.continuous |>.norm.aestronglyMeasurable)
    filter_upwards with x
    simpa only [norm_norm, Function.comp_apply] using (hM _ (hmem x)).trans (le_max_left _ _)
  have hintH : Integrable (fun x : E => ‖fderiv ℝ H x‖) μ := by
    apply hint.mono' (by have hc := hH.continuous_fderiv (by norm_num); fun_prop)
    filter_upwards with x
    simpa only [norm_norm] using hnorm x
  have hp := GaussianPoincare.rotation_first_moment H hH (le_max_right M 0) hdB hB'
  have hmeasure : MeasurePreserving Ψ μ cube := ⟨Ψ_contDiff.continuous.measurable, Ψ_map⟩
  have hprod := hmeasure.prod hmeasure
  have heL : (∫ z : E × E, |H z.1-H z.2| ∂μ.prod μ) =
      ∫ z : E × E, |h z.1-h z.2| ∂((cube (m := m)).prod cube) := by
    rw [← hprod.map_eq]
    exact (integral_map (f := fun z : E × E => |h z.1-h z.2|) hprod.measurable.aemeasurable (by fun_prop)).symm
  have heR : (∫ x : E, ‖fderiv ℝ h (Ψ x)‖ ∂μ) = ∫ x : E, ‖fderiv ℝ h x‖ ∂cube := by
    rw [← hmeasure.map_eq]
    exact (integral_map (f := fun x : E => ‖fderiv ℝ h x‖) hmeasure.measurable.aemeasurable
      (by have hc := hh.continuous_fderiv (by norm_num); fun_prop)).symm
  rw [← heL, ← heR]
  exact hp.trans (mul_le_mul_of_nonneg_left (integral_mono hintH hint hnorm) (by positivity))

theorem uniform_cube_first_moment_oai (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : ContDiff ℝ 1 h) :
    (∫ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), |h z.1 - h z.2| ∂
      (((Measure.pi (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map
          (WithLp.toLp 2)).prod
        ((Measure.pi (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map
          (WithLp.toLp 2)))) ≤
      (Real.pi / 2) * ∫ x, ‖fderiv ℝ h x‖ ∂((Measure.pi
        (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map (WithLp.toLp 2)) :=
  cube_first_moment_core h hh

end UniformSparsestCut.CubePoincare

end

end OAI
end

theorem solution : type_of% @OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment_oai := @OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment_oai
