-- Prove2me | solution 1 for OAI.PlanarFalconer.finite_radial_testNorm_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:22:52.620076+00:00
-- url     : https://prove2.me/submissions/2737096d-b177-4be0-99a8-4513f30c3baf

import Mathlib
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_GaussianRepresentation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem inverse_power_gaussian_integral {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    d^(-u) = k^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(k*a*d^2)) := by
  have hg : 0 < Real.Gamma (u/2) := Real.Gamma_pos_of_pos (by positivity)
  have hdu : 0 < d^u := Real.rpow_pos_of_pos hd _
  have hku : 0 < k^(u/2) := Real.rpow_pos_of_pos hk _
  have hp : (d^2)^(u/2) = d^u := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : 0 < u/2) (mul_pos hk (sq_pos_of_pos hd))
  have he : (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) =
      (fun a : ℝ => a^(u/2-1)*Real.exp (-((k*d^2)*a))) := by
    funext a
    congr 2
    ring
  rw [he,hi,Real.div_rpow (by norm_num) (mul_nonneg hk.le (sq_nonneg d)),
    Real.one_rpow,Real.mul_rpow hk.le (sq_nonneg d),hp,Real.rpow_neg hd.le]
  field_simp [hg.ne', hdu.ne', hku.ne']

theorem source_inverse_power_gaussian_integral {d u : ℝ} (hd : 0 < d) (hu : 0 < u) :
    d^(-u) = Real.pi^(u/2) / Real.Gamma (u/2) *
      ∫ a : ℝ in Ioi 0, a^(u/2-1) * Real.exp (-(Real.pi*a*d^2)) :=
  inverse_power_gaussian_integral hd hu Real.pi_pos

theorem gaussian_mixture_integrable {d u k : ℝ}
    (hd : 0 < d) (hu : 0 < u) (hk : 0 < k) :
    IntegrableOn (fun a : ℝ => a^(u/2-1)*Real.exp (-(k*a*d^2))) (Ioi 0) volume := by
  by_contra h
  have hi := inverse_power_gaussian_integral hd hu hk
  rw [integral_undef h,mul_zero] at hi
  exact (Real.rpow_pos_of_pos hd (-u)).ne' hi

theorem rieszEnergy_eq_prod (μ : Measure Plane) [SFinite μ] (u : ℝ) :
    rieszEnergy μ u = ∫⁻ z : Plane × Plane, (edist z.1 z.2)^(-u) ∂μ.prod μ := by
  unfold rieszEnergy rieszPotential
  exact lintegral_lintegral (by fun_prop)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierLebesgue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_integral_swap (μ : Measure V) [IsFiniteMeasure μ]
    (f : V → ℂ) (hf : Integrable f) :
    (∫ ξ, f ξ * sourceFourier μ ξ) = ∫ x, 𝓕 f x ∂μ := by
  have hi : Integrable (fun z : V × V =>
      f z.1 * Complex.exp (⟪z.2, (-(2*Real.pi)) • z.1⟫ * Complex.I))
      (volume.prod μ) := by
    apply (hf.norm.comp_fst μ).mono
    · exact hf.aestronglyMeasurable.comp_fst.mul (by fun_prop)
    · filter_upwards with z
      simp [Complex.norm_exp]
  simp only [sourceFourier, charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul, real_inner_comm x ξ]
  ring_nf

theorem sourceFourier_difference (μ : Measure V) [IsFiniteMeasure μ] (ξ : V) :
    sourceFourier (μ ∗ μ.map (fun x => -x)) ξ = (‖sourceFourier μ ξ‖^2 : ℂ) := by
  have hr := charFun_map_smul (μ := μ) (-1 : ℝ) ((-(2*Real.pi)) • ξ)
  simp only [neg_one_smul, charFun_neg] at hr
  rw [sourceFourier, charFun_conv, hr, Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq _

theorem gaussian_lebesgue_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b * ‖ξ‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) hb 0 (0 : V)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem source_gaussian_fourier {b : ℝ} (hb : 0 < b) (x : V) :
    𝓕 (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) x =
      ((Real.pi / b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2 / b) * ‖x‖^2) : ℝ) := by
  have he : (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) =
      (fun ξ : V => Complex.exp (-(b : ℂ) * ‖ξ‖^2)) := by
    funext ξ
    push_cast
    rfl
  rw [he, fourier_gaussian_innerProductSpace (b := (b : ℂ)) hb,
    Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  congr 1
  ring

theorem gaussian_lebesgue_square (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : V, Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2) =
      (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
  let ρ := μ ∗ μ.map (fun x => -x)
  have hf : Integrable (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) :=
    (gaussian_lebesgue_integrable (V := V) hb).ofReal
  have h := sourceFourier_integral_swap ρ _ hf
  simp only [ρ, sourceFourier_difference, source_gaussian_fourier hb] at h
  have hconv : (∫ z : V, Real.exp (-(Real.pi^2/b) * ‖z‖^2) ∂ρ) =
      ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
    rw [show ρ = μ ∗ μ.map (fun x => -x) from rfl, integral_conv]
    · apply integral_congr_ae
      filter_upwards with x
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [sub_eq_add_neg]
    · apply (integrable_const (1 : ℝ)).mono (by fun_prop)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hb.le)) (sq_nonneg _)
  have hc : (∫ ξ : V, (Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2 : ℝ)) =
      ∫ x, (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2/b) * ‖x‖^2) ∂ρ := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal] using h
  rw [hc, integral_const_mul, hconv]

theorem source_scaled_gaussian_identity (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫ x, ∫ y, Real.exp (-(Real.pi*a*‖x-y‖^2)) ∂μ ∂μ) =
      a^(-(Module.finrank ℝ V : ℝ)/2) *
        ∫ ξ : V, Real.exp (-Real.pi*‖ξ‖^2/a) * ‖sourceFourier μ ξ‖^2 := by
  have h := gaussian_lebesgue_square μ (div_pos Real.pi_pos ha)
  have h₁ : Real.pi / (Real.pi/a) = a := by field_simp
  have h₂ : Real.pi^2 / (Real.pi/a) = Real.pi*a := by field_simp
  rw [h₁,h₂] at h
  have he : (fun ξ : V => Real.exp (-(Real.pi/a)*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) =
      (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    funext ξ
    congr 2
    ring
  rw [he] at h
  rw [h, neg_div, Real.rpow_neg ha.le, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne', one_mul]
  simp only [neg_mul, mul_assoc]

theorem gaussian_sourceFourier_integrable (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) := by
  apply ((gaussian_lebesgue_integrable (V := V) hb).mul_const ((μ.real univ)^2)).mono
  · unfold sourceFourier
    fun_prop
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem source_scaled_gaussian_lintegral (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ z : V × V, ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2))) ∂μ.prod μ) =
      ENNReal.ofReal (a^(-(Module.finrank ℝ V : ℝ)/2)) *
        ∫⁻ ξ : V, ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a)) *
          ENNReal.ofReal (‖sourceFourier μ ξ‖^2) := by
  have hi : Integrable (fun z : V × V => Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
      (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hf : Integrable (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    convert gaussian_sourceFourier_integrable μ (div_pos Real.pi_pos ha) using 1
    all_goals try with_reducible_and_instances rfl
    funext ξ
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with z; positivity),
    integral_prod _ hi, source_scaled_gaussian_identity μ ha,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hf (by filter_upwards with ξ; positivity)]
  congr 1
  apply lintegral_congr
  intro ξ
  exact ENNReal.ofReal_mul (Real.exp_pos _).le

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_MellinGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_Ioi_inv (g : ℝ → ℝ≥0∞) :
    (∫⁻ t : ℝ in Ioi 0, g t) =
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal ((a^2)⁻¹) * g a⁻¹ := by
  have him : (fun a : ℝ => a⁻¹) '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (inv_pos.mpr (show 0 < a from ha) : 0 < a⁻¹)
    · intro ht
      exact ⟨t⁻¹, (show 0 < t⁻¹ from inv_pos.mpr ht), inv_inv t⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := fun a : ℝ => a⁻¹) (f' := fun a => -(a^2)⁻¹)
    measurableSet_Ioi
    (fun a ha => (hasDerivAt_inv (ne_of_gt ha)).hasDerivWithinAt)
    (fun a _ b _ hab => inv_injective hab) g
  rw [him] at h
  simpa only [abs_neg, abs_inv, abs_pow, sq_abs] using h

theorem inverse_mellin_power {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (a^2)⁻¹ * (a⁻¹)^(v-1) = a^(-v-1) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
    ← Real.rpow_two, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring

theorem inverse_gaussian_mellin {v k : ℝ} (hv : 0 < v) (hk : 0 < k) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(-v-1)*Real.exp (-k/a))) =
      ENNReal.ofReal ((1/k)^v * Real.Gamma v) := by
  have hi : IntegrableOn (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) (Ioi 0) := by
    by_contra hn
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk
    rw [integral_undef hn] at h
    exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hk) v) (Real.Gamma_pos_of_pos hv)).ne' h.symm
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  conv_rhs => rw [lintegral_Ioi_inv]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inverse_mellin_power ha]
  congr 1
  congr 1
  ring_nf

theorem lintegral_Ioi_power_eq_top (v : ℝ) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^v)) = ∞ := by
  by_contra hn
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun a : ℝ => a^v) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact Real.rpow_nonneg ha.le _
  have hi := (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hnon).mp hn
  exact not_integrableOn_Ioi_rpow v hi

theorem source_kernel_gaussian_mixture_all {d u : ℝ} (hd : 0 ≤ d) (hu : 0 < u) :
    (ENNReal.ofReal d)^(-u) =
      ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
          ENNReal.ofReal (Real.exp (-(Real.pi*a*d^2))) := by
  rcases eq_or_lt_of_le hd with hzero | hpos
  · subst d
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hu),
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, mul_one, lintegral_Ioi_power_eq_top]
    have hc : 0 < ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) := by
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
    exact (ENNReal.mul_top hc.ne').symm
  · have hi := gaussian_mixture_integrable hpos hu Real.pi_pos
    have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun a : ℝ => a^(u/2-1)*Real.exp (-(Real.pi*a*d^2))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
      exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.exp_pos _).le
    rw [ENNReal.ofReal_rpow_of_pos hpos,
      source_inverse_power_gaussian_integral hpos hu, ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal hi hnon]
    congr 1
    apply lintegral_congr
    intro a
    exact ENNReal.ofReal_mul' (Real.exp_pos _).le

theorem source_mellin_coefficient {d : ℝ} (hd : 0 < d) (n u : ℝ) :
    (1/(Real.pi*d^2))^((n-u)/2) * Real.Gamma ((n-u)/2) =
      ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) * d^(u-n) := by
  have hp : (d^2)^((n-u)/2) = d^(n-u) := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  rw [show 1/(Real.pi*d^2) = (1/Real.pi)*(d^2)⁻¹ by ring,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity), hp,
    ← Real.rpow_neg hd.le]
  rw [show -(n-u) = u-n by ring]
  ring

theorem source_weight_gaussian_mixture {d : ℝ} (hd : 0 < d) {n u : ℝ} (hun : u < n) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*d^2/a))) =
      ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) *
        ENNReal.ofReal (d^(u-n)) := by
  have h := inverse_gaussian_mellin (v := (n-u)/2) (k := Real.pi*d^2)
    (by linarith) (by positivity)
  rw [source_mellin_coefficient hd n u, ENNReal.ofReal_mul (by positivity)] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), ← Real.rpow_add ha,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceEnergyConstant_pos {n u : ℝ} (hu : 0 < u) (hun : u < n) :
    0 < sourceEnergyConstant n u := by
  unfold sourceEnergyConstant
  apply mul_pos
  · exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos (by linarith))

theorem rieszEnergyOn_gaussian_mixture (μ : Measure V) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    rieszEnergyOn μ u = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a := by
  let F : ℝ → V × V → ℝ≥0∞ := fun a z => ENNReal.ofReal (a^(u/2-1)) *
    ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
  calc
    rieszEnergyOn μ u = ∫⁻ z : V × V,
        ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
          (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ := by
      apply lintegral_congr
      intro z
      rw [edist_dist, dist_eq_norm]
      exact source_kernel_gaussian_mixture_all (norm_nonneg _) hu
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ z : V × V, (∫⁻ a : ℝ in Ioi 0, F a z) ∂μ.prod μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ∫⁻ z : V × V, F a z ∂μ.prod μ := by
      congr 1
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (V × V) × ℝ => F z.2 z.1) := by
        dsimp [F]
        fun_prop
      exact hm.aemeasurable
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro a
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem source_fourier_energy_identity
    (μ : Measure V) [IsFiniteMeasure μ] {u : ℝ}
    (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn μ u = ENNReal.ofReal (sourceEnergyConstant (Module.finrank ℝ V) u) *
      ∫⁻ ξ : V, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-Module.finrank ℝ V)) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by exact_mod_cast hu.trans hun)
  let n : ℝ := Module.finrank ℝ V
  let A : ℝ → ℝ≥0∞ := fun a => ENNReal.ofReal (a^(u/2-1)) * ENNReal.ofReal (a^(-n/2))
  let G : ℝ → V → ℝ≥0∞ := fun a ξ =>
    ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))
  let H : V → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖sourceFourier μ ξ‖^2)
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2))
  have hscale : (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) * gaussianQuadraticOn μ a) =
      ∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    rw [gaussianQuadraticOn, source_scaled_gaussian_lintegral μ ha, ← mul_assoc]
    exact (lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm.trans
        (lintegral_congr (fun ξ => by simp only [A,G,H,n,mul_assoc]))
  have hswap : (∫⁻ a : ℝ in Ioi 0, ∫⁻ ξ : V, A a * G a ξ * H ξ) =
      ∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ := by
    apply lintegral_lintegral_swap
    have hm : Measurable (fun z : ℝ × V => A z.1 * G z.1 z.2 * H z.2) := by
      dsimp [A,G,H,sourceFourier]
      fun_prop
    exact hm.aemeasurable
  have hweight : (∫⁻ ξ : V, ∫⁻ a : ℝ in Ioi 0, A a * G a ξ * H ξ) =
      D * ∫⁻ ξ : V, H ξ * ENNReal.ofReal (‖ξ‖^(u-n)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    have hne : ∀ᵐ ξ : V ∂volume, ξ ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with ξ hξ
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    change (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a))) * H ξ = _
    rw [source_weight_gaussian_mixture (norm_pos_iff.mpr hξ) hun]
    dsimp [D,n]
    ac_rfl
  rw [rieszEnergyOn_gaussian_mixture μ hu,hscale,hswap,hweight,← mul_assoc]
  rw [sourceEnergyConstant,ENNReal.ofReal_mul (by positivity)]

theorem rieszEnergyOn_plane (μ : Measure Plane) [IsFiniteMeasure μ] (u : ℝ) :
    rieszEnergyOn μ u = rieszEnergy μ u := (rieszEnergy_eq_prod μ u).symm

theorem planar_fourier_energy_identity (μ : Measure Plane) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hu2 : u < 2) :
    rieszEnergy μ u = ENNReal.ofReal (sourceEnergyConstant 2 u) *
      ∫⁻ ξ : Plane, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (‖ξ‖^(u-2)) := by
  have hn : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have h := source_fourier_energy_identity μ hu (by simpa [hn] using hu2)
  simpa only [hn, Nat.cast_ofNat, rieszEnergyOn_plane] using h

theorem line_fourier_energy_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    rieszEnergyOn μ u = ENNReal.ofReal (sourceEnergyConstant 1 u) *
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) *
        ENNReal.ofReal (|ξ|^(u-1)) := by
  simpa using source_fourier_energy_identity μ hu (by simpa using hu1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem sine_power_domination {v x : ℝ} (hv : 0 < v) (hx : |x| ≤ Real.pi/2) :
    ‖|Real.sin x|^(-v)‖ ≤ (2/Real.pi)^(-v) * |x|^(-v) := by
  by_cases hz : x = 0
  · subst x
    simp [Real.zero_rpow (neg_ne_zero.mpr hv.ne')]
  · have hxpos : 0 < |x| := abs_pos.mpr hz
    have hc : 0 < 2/Real.pi := by positivity
    have hs := Real.mul_abs_le_abs_sin hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |Real.sin x|^(-v) ≤ ((2/Real.pi)*|x|)^(-v) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hc hxpos) hs (by linarith)
      _ = _ := Real.mul_rpow hc.le hxpos.le

theorem intervalIntegrable_sine_power {v : ℝ} (hv : 0 < v) (hv1 : v < 1)
    (a b : ℝ) : IntervalIntegrable (fun θ : ℝ => |Real.sin θ|^(-v)) volume a b := by
  have hi : IntegrableOn (fun θ : ℝ => |Real.sin θ|^(-v)) (ball 0 (Real.pi/2)) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (by simpa using hv1)
      (C := (2/Real.pi)^(-v))
    · filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx
      rw [mem_ball_zero_iff] at hx
      simpa only [Real.norm_eq_abs] using sine_power_domination hv hx.le
    · have hm : Measurable (fun θ : ℝ => |Real.sin θ|^(-v)) := by fun_prop
      exact hm.aestronglyMeasurable
  have hj : IntervalIntegrable (fun θ : ℝ => |Real.sin θ|^(-v)) volume
      (-Real.pi/2) (Real.pi/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])]
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add, neg_div] using hi
  have hp : Function.Periodic (fun θ : ℝ => |Real.sin θ|^(-v)) Real.pi := by
    intro θ
    simp
  apply hp.intervalIntegrable Real.pi_ne_zero (t := -Real.pi/2) _ a b
  simpa only [show -Real.pi / 2 + Real.pi = Real.pi / 2 by ring] using hj

theorem sine_ne_zero_ae : ∀ᵐ θ : ℝ ∂volume, Real.sin θ ≠ 0 := by
  have he : {θ : ℝ | Real.sin θ = 0} = range (fun n : ℤ => (n : ℝ)*Real.pi) := by
    ext θ
    simp only [mem_ofPred_eq,mem_range,Real.sin_eq_zero_iff]
  rw [ae_iff]
  simp only [not_not]
  change volume {θ : ℝ | Real.sin θ = 0} = 0
  rw [he]
  exact (countable_range _).measure_zero volume

theorem sineKernel_lintegral_eq {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (a b : ℝ) :
    (∫⁻ θ : ℝ in Ioc a b, sineKernel v θ) =
      ENNReal.ofReal (∫ θ : ℝ in Ioc a b, |Real.sin θ|^(-v)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (intervalIntegrable_sine_power hv hv1 a b).1
    (Filter.Eventually.of_forall (fun θ => Real.rpow_nonneg (abs_nonneg _) _))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae sine_ne_zero_ae] with θ hθ
  exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hθ)

theorem sineKernel_lintegral_lt_top {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (a b : ℝ) :
    (∫⁻ θ : ℝ in Ioc a b, sineKernel v θ) < ∞ := by
  rw [sineKernel_lintegral_eq hv hv1]
  exact ENNReal.ofReal_lt_top

theorem one_le_sineKernel {v : ℝ} (hv : 0 ≤ v) (θ : ℝ) : 1 ≤ sineKernel v θ := by
  have hbase : ENNReal.ofReal |Real.sin θ| ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (Real.abs_sin_le_one θ)
  simpa only [sineKernel,ENNReal.rpow_zero] using
    ENNReal.rpow_le_rpow_of_exponent_ge hbase (show -v ≤ 0 by linarith)

theorem angularEnergyConstant_lt_top {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    angularEnergyConstant v < ∞ := sineKernel_lintegral_lt_top hv hv1 _ _

theorem sine_shift_ne_zero_ae (c : ℝ) :
    ∀ᵐ θ : ℝ ∂volume, Real.sin (θ-c) ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  apply measure_mono_null (t := range (fun n : ℤ => (n : ℝ)*Real.pi+c))
  · intro θ hθ
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hθ
    exact ⟨n,by linarith⟩
  · exact (countable_range _).measure_zero volume

theorem sineKernel_shift_integral {v : ℝ} (hv : 0 < v) (hv1 : v < 1) (c : ℝ) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v (θ-c)) = angularEnergyConstant v := by
  let f : ℝ → ℝ := fun θ => |Real.sin θ|^(-v)
  have hp : Function.Periodic f (2*Real.pi) := by intro θ; simp [f]
  have hi : IntervalIntegrable (fun θ => f (θ-c)) volume 0 (2*Real.pi) := by
    simpa only [f, neg_add_cancel, sub_add_cancel] using
      (intervalIntegrable_sine_power hv hv1 (-c) (2*Real.pi-c)).comp_sub_right c
  have hnon : ∀ θ, 0 ≤ f θ := fun θ => Real.rpow_nonneg (abs_nonneg _) _
  have he : (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), sineKernel v (θ-c)) =
      ENNReal.ofReal (∫ θ : ℝ in Ioc 0 (2*Real.pi), f (θ-c)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall (fun θ => hnon (θ-c)))]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (sine_shift_ne_zero_ae c)] with θ hθ
    exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hθ)
  rw [he,angularEnergyConstant,sineKernel_lintegral_eq hv hv1]
  congr 1
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi),
    intervalIntegral.integral_comp_sub_right]
  rw [zero_sub]
  change (∫ x in -c..2*Real.pi-c, f x) = ∫ x in Ioc 0 (2*Real.pi), f x
  rw [show 2*Real.pi-c = -c+2*Real.pi by ring,
    hp.intervalIntegral_add_eq (-c) 0,zero_add,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceProjection_sub (θ : ℝ) (x y : Plane) :
    sourceProjection θ (x-y) = sourceProjection θ x - sourceProjection θ y := by
  simp only [sourceProjection,PiLp.sub_apply]
  ring

theorem abs_sourceProjection (θ : ℝ) {z : Plane} (hz : z ≠ 0) :
    |sourceProjection θ z| = ‖z‖ * |Real.sin (θ-planePhase z)| := by
  let w := Complex.orthonormalBasisOneI.repr.symm z
  have hw : w ≠ 0 := by
    intro h
    have hn := congrArg norm h
    simp only [w,LinearIsometryEquiv.norm_map,norm_zero] at hn
    exact hz (norm_eq_zero.mp hn)
  have hn : ‖w‖ = ‖z‖ := LinearIsometryEquiv.norm_map _ _
  have hre : w.re = z 0 := by simp [w,Complex.orthonormalBasisOneI_repr_symm_apply]
  have him : w.im = z 1 := by simp [w,Complex.orthonormalBasisOneI_repr_symm_apply]
  have he : sourceProjection θ z = -‖z‖ * Real.sin (θ-planePhase z) := by
    rw [Real.sin_sub]
    change -Real.sin θ*z 0+Real.cos θ*z 1 =
      -‖z‖*(Real.sin θ*Real.cos (Complex.arg w)-Real.cos θ*Real.sin (Complex.arg w))
    rw [Complex.cos_arg hw,Complex.sin_arg,hre,him,hn]
    field_simp [norm_ne_zero_iff.mpr hz]
    ring
  rw [he,abs_mul,abs_neg,abs_norm]

theorem sourceProjection_kernel_factor {t : ℝ} (ht : 0 < t) (θ : ℝ) (z : Plane) :
    (ENNReal.ofReal |sourceProjection θ z|)^(-t) =
      (ENNReal.ofReal ‖z‖)^(-t) * sineKernel t (θ-planePhase z) := by
  by_cases hz : z = 0
  · subst z
    simp only [sourceProjection,PiLp.zero_apply,mul_zero,add_zero,abs_zero,norm_zero,
      ENNReal.ofReal_zero,ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr ht)]
    exact (ENNReal.top_mul (ne_of_gt (zero_lt_one.trans_le
      (one_le_sineKernel ht.le _)))).symm
  · rw [abs_sourceProjection θ hz,ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    rfl

theorem projected_energy_formula (μ : Measure Plane) [IsFiniteMeasure μ] (t θ : ℝ) :
    rieszEnergyOn (projectedMeasure μ θ) t =
      ∫⁻ z : Plane × Plane, (ENNReal.ofReal |sourceProjection θ (z.1-z.2)|)^(-t) ∂μ.prod μ := by
  have hm : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  rw [rieszEnergyOn,projectedMeasure,Measure.map_prod_map μ μ hm hm,
    lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map,edist_dist,Real.dist_eq,sourceProjection_sub]

theorem differenceEnergyMeasure_mass (μ : Measure Plane) (t : ℝ) :
    differenceEnergyMeasure μ t univ = rieszEnergyOn μ t := by
  rw [differenceEnergyMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  rfl

theorem projected_energy_weighted_formula (μ : Measure Plane) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    rieszEnergyOn (projectedMeasure μ θ) t =
      ∫⁻ z : Plane × Plane, sineKernel t (θ-planePhase (z.1-z.2))
        ∂differenceEnergyMeasure μ t := by
  rw [projected_energy_formula,differenceEnergyMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (by unfold sineKernel planePhase; fun_prop)]
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply]
  rw [sourceProjection_kernel_factor ht,edist_dist,dist_eq_norm]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierSlice
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

theorem inner_sourceNormal (θ : ℝ) (x : Plane) :
    ⟪x, sourceNormal θ⟫ = sourceProjection θ x := by
  simp [sourceNormal, sourceProjection, PiLp.inner_apply, Fin.sum_univ_two]

theorem source_fourier_slice (μ : Measure Plane) [IsFiniteMeasure μ] (θ ξ : ℝ) :
    sourceFourier (projectedMeasure μ θ) ξ = sourceFourier μ (ξ • sourceNormal θ) := by
  simp only [sourceFourier, charFun_apply, projectedMeasure]
  rw [integral_map (by unfold sourceProjection; fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  simp only [inner_smul_right, inner_sourceNormal, Real.inner_apply, smul_eq_mul]
  congr 1
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SliceAverage
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

theorem periodic_lintegral_interval {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f T) (a : ℝ) :
    (∫⁻ θ in Ioc a (a+T), f θ) = ∫⁻ θ in Ioc 0 T, f θ := by
  let : Fact (0 < T) := ⟨hT⟩
  have h₁ := AddCircle.lintegral_preimage T a hf.lift
  have h₂ := AddCircle.lintegral_preimage T 0 hf.lift
  simpa using h₁.trans h₂.symm

theorem periodic_lintegral_shift {T : ℝ} (hT : 0 < T)
    (f : ℝ → ℝ≥0∞) (hf : Function.Periodic f T) (c : ℝ) :
    (∫⁻ θ in Ioc 0 T, f (θ+c)) = ∫⁻ θ in Ioc 0 T, f θ := by
  let : Fact (0 < T) := ⟨hT⟩
  have h₁ := AddCircle.lintegral_preimage T 0
    (fun θ : AddCircle T => hf.lift (θ+(c : AddCircle T)))
  have h₂ := AddCircle.lintegral_preimage T 0 hf.lift
  have h₃ := lintegral_add_right_eq_self (μ := (volume : Measure (AddCircle T))) hf.lift (c : AddCircle T)
  simpa only [zero_add, ← QuotientAddGroup.mk_add, Function.Periodic.lift_coe] using h₁.trans (h₃.trans h₂.symm)

theorem normal_eq_direction (θ : ℝ) :
    sourceNormal θ = sourceDirection (θ+Real.pi/2) := by
  ext i
  fin_cases i <;> simp [sourceNormal, sourceDirection,
    Complex.orthonormalBasisOneI_repr_apply, Real.cos_add, Real.sin_add, -Complex.ofReal_sin, -Complex.ofReal_cos]

theorem sourceDirection_periodic : Function.Periodic sourceDirection (2*Real.pi) := by
  intro θ
  simp [sourceDirection]

theorem plane_polar_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * f (r • sourceDirection θ)) = ∫⁻ z : Plane, f z := by
  have h := Complex.lintegral_comp_polarCoord_symm
    (fun z => f (Complex.orthonormalBasisOneI.repr z))
  have hμ := (LinearIsometryEquiv.measurePreserving
    Complex.orthonormalBasisOneI.repr).lintegral_comp_emb
      Complex.orthonormalBasisOneI.repr.toHomeomorph.measurableEmbedding f
  rw [hμ] at h
  change (∫⁻ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * f (Complex.orthonormalBasisOneI.repr
      (Complex.polarCoord.symm p))) = _ at h
  have he (r θ : ℝ) : Complex.orthonormalBasisOneI.repr
      (Complex.polarCoord.symm (r,θ)) = r • sourceDirection θ := by
    rw [Complex.polarCoord_symm_apply]
    change Complex.orthonormalBasisOneI.repr (r • (Real.cos θ + Real.sin θ * Complex.I)) = _
    exact Complex.orthonormalBasisOneI.repr.map_smul r _
  simp_rw [he] at h
  change (∫⁻ p : ℝ × ℝ, ENNReal.ofReal p.1 * f (p.1 • sourceDirection p.2)
    ∂(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)) = _ at h
  rw [← Measure.prod_restrict, lintegral_prod _ (by fun_prop)] at h
  have hm : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 * f (p.1 • sourceDirection p.2)) := by fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable] at h
  rw [restrict_Ioo_eq_restrict_Ioc] at h
  let F : ℝ → ℝ≥0∞ := fun θ => ∫⁻ r in Ioi (0:ℝ),
    ENNReal.ofReal r * f (r • sourceDirection θ)
  have hF : Function.Periodic F (2*Real.pi) := by
    intro θ
    simp only [F,sourceDirection_periodic θ]
  have ha := periodic_lintegral_interval (by positivity : 0 < 2*Real.pi) F hF (-Real.pi)
  have hend : -Real.pi+2*Real.pi = Real.pi := by ring
  rw [hend] at ha
  exact ha.symm.trans h

theorem plane_polar_weighted_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      f (r • sourceDirection θ) * ENNReal.ofReal (r^(s-1))) =
        ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  rw [← plane_polar_lintegral _ (by fun_prop)]
  apply lintegral_congr
  intro θ
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [norm_smul, norm_sourceDirection, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hpow : r * r^(s-2) = r^(s-1) := by
    nth_rw 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [mul_left_comm, ← ENNReal.ofReal_mul hr.le, hpow]

theorem normal_polar_weighted_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      f (r • sourceNormal θ) * ENNReal.ofReal (r^(s-1))) =
        ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  simp_rw [normal_eq_direction]
  let F : ℝ → ℝ≥0∞ := fun θ => ∫⁻ r in Ioi (0:ℝ),
    f (r • sourceDirection θ) * ENNReal.ofReal (r^(s-1))
  have hF : Function.Periodic F (2*Real.pi) := by
    intro θ
    simp only [F,sourceDirection_periodic θ]
  exact (periodic_lintegral_shift (by positivity) F hF (Real.pi/2)).trans
    (plane_polar_weighted_lintegral f hf s)

theorem even_lintegral_real (f : ℝ → ℝ≥0∞) (he : ∀ x, f (-x) = f x) :
    (∫⁻ r : ℝ, f r) = 2 * ∫⁻ r in Ioi (0:ℝ), f r := by
  have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ)) ((Ioi (0:ℝ)).indicator f)
  have hi (x : ℝ) : (Ioi (0:ℝ)).indicator f (-x) = (Iio (0:ℝ)).indicator f x := by
    by_cases hx : x < 0 <;> simp [Set.indicator, hx, he]
  simp_rw [hi] at h
  rw [lintegral_indicator measurableSet_Iio,lintegral_indicator measurableSet_Ioi] at h
  rw [← lintegral_add_compl f measurableSet_Ioi,compl_Ioi,
    ← restrict_Iio_eq_restrict_Iic,h,two_mul]

theorem even_polar_slice_average (f : Plane → ℝ≥0∞) (hf : Measurable f)
    (he : ∀ z, f (-z) = f z) (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r : ℝ,
      f (r • sourceNormal θ) * ENNReal.ofReal (|r|^(s-1))) =
        2 * ∫⁻ z : Plane, f z * ENNReal.ofReal (‖z‖^(s-2)) := by
  have h (θ : ℝ) : (∫⁻ r : ℝ,
      f (r • sourceNormal θ) * ENNReal.ofReal (|r|^(s-1))) =
      2 * ∫⁻ r in Ioi (0:ℝ), f (r • sourceNormal θ) * ENNReal.ofReal (r^(s-1)) := by
    rw [even_lintegral_real _ (by intro r; simp only [neg_smul, he,abs_neg])]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    rw [abs_of_pos hr]
  simp_rw [h]
  rw [lintegral_const_mul' _ _ (by norm_num),normal_polar_weighted_lintegral f hf s]

theorem source_slice_average (μ : Measure Plane) [IsFiniteMeasure μ] (s : ℝ) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy μ s θ) =
      2 * ∫⁻ z : Plane, ENNReal.ofReal (‖sourceFourier μ z‖^2) *
        ENNReal.ofReal (‖z‖^(s-2)) := by
  unfold sourceSliceEnergy
  refine even_polar_slice_average (fun z => ENNReal.ofReal (‖sourceFourier μ z‖^2))
    (by unfold sourceFourier; fun_prop) ?_ s
  intro z
  simp [sourceFourier,smul_neg,charFun_neg]

theorem source_slice_average_energy (μ : Measure Plane) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    ENNReal.ofReal (sourceEnergyConstant 2 s) *
      (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy μ s θ) = 2 * rieszEnergy μ s := by
  rw [source_slice_average,planar_fourier_energy_identity μ hs hs2,mul_left_comm]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FourierConvolution
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem sourceFourier_convolution (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (ξ : V) :
    sourceFourier (μ ∗ ν) ξ = sourceFourier μ ξ * sourceFourier ν ξ := by
  exact charFun_conv _

theorem sourceFourier_convolution_norm_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (ξ : V) :
    ‖sourceFourier (μ ∗ ν) ξ‖ ≤ ‖sourceFourier μ ξ‖ := by
  rw [sourceFourier_convolution,norm_mul]
  have norm_bound : ‖sourceFourier ν ξ‖ ≤ 1 :=
    norm_charFun_le_one (μ := ν) ((-(2 * Real.pi)) • ξ)
  exact (mul_le_mul_of_nonneg_left norm_bound (norm_nonneg _)).trans_eq (mul_one _)

theorem rieszEnergyOn_convolution_probability_le (μ ν : Measure V) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 < u) (hun : u < Module.finrank ℝ V) :
    rieszEnergyOn (μ ∗ ν) u ≤ rieszEnergyOn μ u := by
  rw [source_fourier_energy_identity (μ ∗ ν) hu hun,source_fourier_energy_identity μ hu hun]
  apply mul_le_mul_right
  apply lintegral_mono
  intro ξ
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg _) (sourceFourier_convolution_norm_le μ ν ξ) 2

theorem rieszEnergy_convolution_probability_le (μ ν : Measure Plane) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] {u : ℝ} (hu : 0 < u) (hu2 : u < 2) :
    rieszEnergy (μ ∗ ν) u ≤ rieszEnergy μ u := by
  rw [← rieszEnergyOn_plane,← rieszEnergyOn_plane]
  exact rieszEnergyOn_convolution_probability_le μ ν hu (by simpa [Plane] using hu2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem density_energy_holder (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q u : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) :
    rieszEnergyOn (μ.withDensity h) u ≤ (rieszEnergyOn μ (u*p))^(1/p) := by
  let K : V × V → ℝ≥0∞ := fun z => (edist z.1 z.2)^(-u)
  let H : V × V → ℝ≥0∞ := fun z => h z.1*h z.2
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hH : Measurable H := by dsimp [H]; fun_prop
  have he : rieszEnergyOn (μ.withDensity h) u = ∫⁻ z : V × V, (K*H) z ∂μ.prod μ := by
    rw [rieszEnergyOn, prod_withDensity hh hh,
      lintegral_withDensity_eq_lintegral_mul _ hH hK]
    apply lintegral_congr
    intro z
    exact mul_comm _ _
  have hp : (∫⁻ z : V × V, (K z)^p ∂μ.prod μ) = rieszEnergyOn μ (u*p) := by
    apply lintegral_congr
    intro z
    dsimp [K]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hq : (∫⁻ z : V × V, (H z)^q ∂μ.prod μ) = 1 := by
    simp_rw [H, ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg]
    rw [lintegral_prod_mul (f := fun x => h x^q) (g := fun x => h x^q)
      (by fun_prop) (by fun_prop),hnorm,mul_one]
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod μ) hpq
    hK.aemeasurable hH.aemeasurable
  simpa only [← he,hp,hq,ENNReal.one_rpow,mul_one] using hb

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem finiteMeasure_normalized_density (μ : Measure V) [IsFiniteMeasure μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1) : IsFiniteMeasure (μ.withDensity h) := by
  have hb := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun _ => 1) (g := h) measurable_const.aemeasurable hh.aemeasurable
  simp only [Pi.mul_apply,one_mul,ENNReal.one_rpow,lintegral_const,hnorm,mul_one] at hb
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hb.trans_lt (ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hpq.nonneg) (measure_ne_top _ _))

theorem bounded_riesz_kernel {d D u t : ℝ} (hd : 0 ≤ d) (hD : 0 < D)
    (hdD : d ≤ D) (hu : 0 < u) (hut : u < t) :
    (ENNReal.ofReal d)^(-u) ≤ ENNReal.ofReal (D^(t-u)) * (ENNReal.ofReal d)^(-t) := by
  rcases eq_or_lt_of_le hd with hz | hp
  · subst d
    rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.zero_rpow_of_neg (by linarith), ENNReal.mul_top
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hD _)).ne']
  · rw [ENNReal.ofReal_rpow_of_pos hp, ENNReal.ofReal_rpow_of_pos hp,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      d^(-u) = d^(t-u)*d^(-t) := by rw [← Real.rpow_add hp]; congr 1; ring
      _ ≤ D^(t-u)*d^(-t) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hp.le hdD (sub_pos.mpr hut).le) (Real.rpow_nonneg hp.le _)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
theorem bounded_riesz_energy (μ : Measure V) [SFinite μ] {D u t : ℝ}
    (hD : 0 < D) (hu : 0 < u) (hut : u < t)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn μ u ≤ ENNReal.ofReal (D^(t-u)) * rieszEnergyOn μ t := by
  rw [rieszEnergyOn,rieszEnergyOn,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hdiam] with z hz
  rw [edist_dist]
  exact bounded_riesz_kernel dist_nonneg hD hz hu hut

theorem density_energy_of_diameter (μ : Measure V) [SFinite μ]
    (h : V → ℝ≥0∞) (hh : Measurable h) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hD : 0 < D) (hupt : u*p < t)
    (hnorm : (∫⁻ x, (h x)^q ∂μ) = 1)
    (hdiam : ∀ᵐ z : V × V ∂μ.prod μ, dist z.1 z.2 ≤ D) :
    rieszEnergyOn (μ.withDensity h) u ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn μ t)^(1/p) := by
  exact (density_energy_holder μ h hh hpq hnorm).trans
    (ENNReal.rpow_le_rpow (bounded_riesz_energy μ hD (mul_pos hu hpq.pos) hupt hdiam)
      (one_div_nonneg.mpr hpq.nonneg))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem weighted_power_cancel {x : ℝ} (hx : 0 < x) (A B a : ℝ) :
    (A*x^a)*(B*x^(-a)) = A*B := by
  calc
    _ = (A*B)*(x^a*x^(-a)) := by ring
    _ = _ := by rw [← Real.rpow_add hx,add_neg_cancel,Real.rpow_zero,mul_one]

theorem weighted_power_square {x : ℝ} (hx : 0 ≤ x) (A a : ℝ) :
    (A*x^(a/2))^2 = A^2*x^a := by
  rw [mul_pow, ← Real.rpow_mul_natCast hx]
  congr 2
  ring

theorem line_weighted_cauchy (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x) (u : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (F x*G x)) ≤
      (∫⁻ x : ℝ, ENNReal.ofReal ((F x)^2*|x|^(1-u)))^(1/2 : ℝ) *
      (∫⁻ x : ℝ, ENNReal.ofReal ((G x)^2*|x|^(u-1)))^(1/2 : ℝ) := by
  let A : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (F x * |x|^((1-u)/2))
  let B : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (G x * |x|^((u-1)/2))
  have hA : Measurable A := by dsimp [A]; fun_prop
  have hB : Measurable B := by dsimp [B]; fun_prop
  have hprod : (∫⁻ x : ℝ, ENNReal.ofReal (F x*G x)) = ∫⁻ x : ℝ, (A*B) x := by
    apply lintegral_congr_ae
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with x hx
    dsimp [A,B]
    rw [← ENNReal.ofReal_mul (mul_nonneg (hFn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      show (u-1)/2 = -((1-u)/2) by ring,
      weighted_power_cancel (abs_pos.mpr hx)]
  have hsqA : (∫⁻ x : ℝ, A x^(2 : ℝ)) =
      ∫⁻ x : ℝ, ENNReal.ofReal ((F x)^2*|x|^(1-u)) := by
    apply lintegral_congr
    intro x
    dsimp [A]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hFn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      weighted_power_square (abs_nonneg x)]
  have hsqB : (∫⁻ x : ℝ, B x^(2 : ℝ)) =
      ∫⁻ x : ℝ, ENNReal.ofReal ((G x)^2*|x|^(u-1)) := by
    apply lintegral_congr
    intro x
    dsimp [B]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (mul_nonneg (hGn x) (Real.rpow_nonneg (abs_nonneg x) _)),
      weighted_power_square (abs_nonneg x)]
  rw [hprod, ← hsqA, ← hsqB]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable

theorem schwartz_measure_pairing (μ : Measure ℝ) [IsFiniteMeasure μ] (f : 𝓢(ℝ, ℂ)) :
    (∫ x, f x ∂μ) = ∫ ξ : ℝ, (𝓕⁻ f) ξ * sourceFourier μ ξ := by
  have h := sourceFourier_integral_swap μ ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (𝓕⁻ f).integrable
  simpa only [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq] using h.symm

theorem schwartz_inverse_weight (f : 𝓢(ℝ, ℂ)) (v : ℝ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕⁻ f) ξ‖^2 * |ξ|^v)) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^v) := by
  have he (ξ : ℝ) : (𝓕⁻ f) ξ = (𝓕 f) (-ξ) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    rfl
  simp_rw [he]
  simpa only [abs_neg] using lintegral_neg_eq_self (μ := volume)
    (fun ξ : ℝ => ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^v))

theorem source_fourier_pairing (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : 𝓢(ℝ, ℂ)) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
        ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      (rieszEnergyOn μ u)^(1/2 : ℝ) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  have hnorm : ENNReal.ofReal (‖∫ x, f x ∂μ‖) ≤
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕⁻ f) ξ‖ * ‖sourceFourier μ ξ‖) := by
    rw [schwartz_measure_pairing]
    simpa only [← ofReal_norm, norm_mul] using enorm_integral_le_lintegral_enorm
      (fun ξ : ℝ => (𝓕⁻ f) ξ * sourceFourier μ ξ)
  have hcs := line_weighted_cauchy (fun ξ => ‖(𝓕⁻ f) ξ‖)
    (fun ξ => ‖sourceFourier μ ξ‖) (by fun_prop)
    (by unfold sourceFourier; fun_prop) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) u
  rw [schwartz_inverse_weight] at hcs
  have h := mul_le_mul_right (hnorm.trans hcs)
    ((ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ))
  rw [line_fourier_energy_identity μ hu hu1,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  have he : (∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2 * |ξ|^(u-1))) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (‖sourceFourier μ ξ‖^2) * ENNReal.ofReal (|ξ|^(u-1)) := by
    apply lintegral_congr
    intro ξ
    exact ENNReal.ofReal_mul (sq_nonneg _)
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ac_rfl

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

theorem exists_normalized_dual_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (hN0 : (∫⁻ x, F x^p ∂μ) ≠ 0) (hNtop : (∫⁻ x, F x^p ∂μ) ≠ ∞) :
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∫⁻ x, h x^q ∂μ) = 1 ∧
      (∫⁻ x, F x*h x ∂μ) = (∫⁻ x, F x^p ∂μ)^(1/p) := by
  let N := ∫⁻ x, F x^p ∂μ
  let h : X → ℝ≥0∞ := fun x => F x^(p-1) * N^(-1/q)
  have hp1 : 0 < p-1 := sub_pos.mpr (Real.holderConjugate_iff.mp hpq).1
  have hc : N^(-1/q) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hN0 hNtop
  refine ⟨h, by dsimp [h]; fun_prop, ?_, ?_⟩
  · have he (x : X) : h x^q = F x^p * N⁻¹ := by
      dsimp [h]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,hpq.sub_one_mul_conj]
      rw [show (-1/q)*q = -1 by field_simp [hpq.symm.pos.ne'], ENNReal.rpow_neg_one]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hN0),
      ENNReal.mul_inv_cancel hN0 hNtop]
  · have he (x : X) : F x*h x = F x^p * N^(-1/q) := by
      dsimp [h]
      have hr := ENNReal.rpow_add_of_nonneg (x := F x) 1 (p-1) zero_le_one hp1.le
      rw [show (1 : ℝ)+(p-1)=p by ring, ENNReal.rpow_one] at hr
      rw [← mul_assoc, ← hr]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ hc]
    change N * N^(-1/q) = N^(1/p)
    conv_lhs => lhs; rw [← ENNReal.rpow_one N]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    congr 1
    have ht := hpq.one_div_add_one_div
    norm_num at ht
    simp only [neg_div,one_div]
    linarith

theorem fiber_dual_test_bound (η : Measure ℝ) [IsFiniteMeasure η]
    (f : 𝓢(ℝ, ℂ)) (h : ℝ → ℝ≥0∞) (hh : Measurable h) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hu1 : u < 1)
    (hD : 0 < D) (hupt : u*p < t) (hnorm : (∫⁻ x, h x^q ∂η) = 1)
    (hdiam : ∀ᵐ z : ℝ × ℝ ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
      ENNReal.ofReal (‖∫ x, f x ∂η.withDensity h‖) ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖(𝓕 f) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  let := finiteMeasure_normalized_density η h hh hpq hnorm
  have hpair := source_fourier_pairing (η.withDensity h) f hu hu1
  have he := density_energy_of_diameter η h hh hpq hu hD hupt hnorm hdiam
  apply hpair.trans
  apply mul_le_mul_left
  have hr := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_mul] at hr
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem source_fiber_lp_bound (η : Measure ℝ) [IsFiniteMeasure η]
    (f : 𝓢(ℝ, ℝ)) (hf : ∀ x, 0 ≤ f x) {D p q u t : ℝ}
    (hpq : p.HolderConjugate q) (hu : 0 < u) (hu1 : u < 1)
    (hD : 0 < D) (hupt : u*p < t)
    (hdiam : ∀ᵐ z : ℝ × ℝ ∂η.prod η, dist z.1 z.2 ≤ D) :
    (ENNReal.ofReal (sourceEnergyConstant 1 u))^(1/2 : ℝ) *
      eLpNorm (fun x => f x) (ENNReal.ofReal p) η ≤
      (ENNReal.ofReal (D^(t-u*p)) * rieszEnergyOn η t)^(1/(2*p)) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal
          (‖(𝓕 (complexSchwartz f)) ξ‖^2 * |ξ|^(1-u)))^(1/2 : ℝ) := by
  let F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let N : ℝ≥0∞ := ∫⁻ x, F x^p ∂η
  have hnorm : eLpNorm (fun x => f x) (ENNReal.ofReal p) η = N^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf x)]
  have hfinite := ((f.memLp_top η).mono_exponent
    (show ENNReal.ofReal p ≤ ∞ from le_top)).eLpNorm_lt_top
  change eLpNorm (fun x => f x) (ENNReal.ofReal p) η < ∞ at hfinite
  rw [hnorm] at hfinite
  have hNtop : N ≠ ∞ := by
    intro ht
    rw [ht, ENNReal.top_rpow_of_pos (one_div_pos.mpr hpq.pos)] at hfinite
    exact lt_irrefl _ hfinite
  rw [hnorm]
  by_cases hN0 : N = 0
  · rw [hN0,ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos),mul_zero]
    exact bot_le
  obtain ⟨h,hh,hq,hdual⟩ := exists_normalized_dual_density η F
    (by dsimp [F]; fun_prop) hpq hN0 hNtop
  let := finiteMeasure_normalized_density η h hh hpq hq
  have hi : Integrable (fun x => f x) (η.withDensity h) :=
    ((f.memLp_top (η.withDensity h)).mono_exponent (show (1 : ℝ≥0∞) ≤ ∞ from le_top)).integrable le_rfl
  have hnormIntegral : ENNReal.ofReal (‖∫ x, (complexSchwartz f) x ∂η.withDensity h‖) = N^(1/p) := by
    change ENNReal.ofReal (‖∫ x, (f x : ℂ) ∂η.withDensity h‖) = _
    rw [integral_complex_ofReal,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg hf),
      ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf),
      lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    rw [← hdual]
    apply lintegral_congr
    intro x
    exact mul_comm _ _
  have hb := fiber_dual_test_bound η (complexSchwartz f) h hh hpq hu hu1 hD hupt hq hdiam
  rwa [hnormIntegral] at hb

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionDensity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceFrame_measurePreserving (θ : ℝ) :
    MeasurePreserving (sourceFrame θ) volume volume := by
  have h₁ : MeasurePreserving (fun p : ℝ × ℝ => p.swap) volume volume :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving (fun p : ℝ × ℝ => Complex.measurableEquivRealProd.symm p)
      volume volume := Complex.volume_preserving_equiv_real_prod.symm
  have h₃ : MeasurePreserving (fun z : ℂ => rotation (Circle.exp θ) z) volume volume :=
    LinearIsometryEquiv.measurePreserving (rotation (Circle.exp θ))
  have h₄ : MeasurePreserving (fun z : ℂ => Complex.orthonormalBasisOneI.repr z) volume volume :=
    LinearIsometryEquiv.measurePreserving Complex.orthonormalBasisOneI.repr
  exact h₄.comp (h₃.comp (h₂.comp h₁))

theorem projectedMeasure_withDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (θ : ℝ) :
    projectedMeasure (volume.withDensity a) θ = volume.withDensity (projectedDensity a θ) := by
  have hP : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  ext S hS
  rw [projectedMeasure,Measure.map_apply hP hS,withDensity_apply _ (hS.preimage hP),
    withDensity_apply _ hS]
  have h := (sourceFrame_measurePreserving θ).setLIntegral_comp_preimage (hS.preimage hP) ha
  have hset : sourceFrame θ ⁻¹' (sourceProjection θ ⁻¹' S) = S ×ˢ univ := by
    ext ⟨z,r⟩
    simp only [mem_preimage,sourceProjection_frame,mem_prod,mem_univ,and_true]
  rw [hset] at h
  change (∫⁻ p : ℝ × ℝ in S ×ˢ univ, a (sourceFrame θ p) ∂volume.prod volume) = _ at h
  rw [setLIntegral_prod _ (by fun_prop)] at h
  simpa only [setLIntegral_univ,projectedDensity] using h.symm

theorem sourceFrame_inverse (θ : ℝ) (x : Plane) :
    sourceFrame θ (sourceProjection θ x,sourceAlong θ x) = x := by
  rw [sourceFrame_eq]
  ext i
  fin_cases i <;>
    simp [sourceProjection,sourceAlong,sourceNormal,sourceDirection,
      Complex.orthonormalBasisOneI_repr_apply,-Complex.ofReal_cos,-Complex.ofReal_sin] <;>
    nlinarith [congrArg (fun a : ℝ => x 0*a) (Real.sin_sq_add_cos_sq θ),
      congrArg (fun a : ℝ => x 1*a) (Real.sin_sq_add_cos_sq θ)]

theorem sourceFrame_line (θ : ℝ) (x : Plane) (r : ℝ) :
    sourceFrame θ (sourceProjection θ x,r+sourceAlong θ x) = x + r • sourceDirection θ := by
  have hx := sourceFrame_inverse θ x
  rw [sourceFrame_eq] at hx
  rw [sourceFrame_eq,add_smul]
  calc
    _ = (sourceProjection θ x • sourceNormal θ + sourceAlong θ x • sourceDirection θ) +
        r • sourceDirection θ := by abel
    _ = _ := by rw [hx]

theorem projectedDensity_line (a : Plane → ℝ≥0∞) (θ : ℝ) (x : Plane) :
    projectedDensity a θ (sourceProjection θ x) = ∫⁻ r : ℝ, a (x+r • sourceDirection θ) := by
  have h := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun r => a (sourceFrame θ (sourceProjection θ x,r))) (sourceAlong θ x)
  simp_rw [sourceFrame_line] at h
  exact h.symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_FiberSchwartz
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform Convolution

theorem sourceFiber_line_compact (a : Plane → ℝ) (hc : HasCompactSupport a) (θ z : ℝ) :
    HasCompactSupport (fun r : ℝ => a (sourceFrame θ (z,r))) := by
  apply HasCompactSupport.intro (hc.image (continuous_sourceAlong θ))
  intro r hr
  by_contra hn
  apply hr
  exact ⟨sourceFrame θ (z,r), subset_tsupport a hn, sourceAlong_frame θ z r⟩

theorem sourceSchwartzFiber_nonneg (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ z : ℝ) :
    0 ≤ sourceSchwartzFiber a hc ha θ z := integral_nonneg (fun _ => hn _)

theorem sourceSchwartzFiber_density (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ z : ℝ) :
    ENNReal.ofReal (sourceSchwartzFiber a hc ha θ z) =
      projectedDensity (fun x => ENNReal.ofReal (a x)) θ z := by
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (ha.continuous.comp ((continuous_sourceFrame θ).comp (by fun_prop))).integrable_of_hasCompactSupport
      (sourceFiber_line_compact a hc θ z)
  · exact Filter.Eventually.of_forall (fun r => hn _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_FiberSlice
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform RealInnerProductSpace

theorem sourceDensityMeasure_finite (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : Continuous a) (hn : ∀ x, 0 ≤ a x) : IsFiniteMeasure (sourceDensityMeasure a) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (ha.integrable_of_hasCompactSupport hc)
    (Filter.Eventually.of_forall hn)]
  exact ENNReal.ofReal_ne_top

theorem sourceSchwartzFiber_measure (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ : ℝ) :
    projectedMeasure (sourceDensityMeasure a) θ =
      volume.withDensity (fun z => ENNReal.ofReal (sourceSchwartzFiber a hc ha θ z)) := by
  rw [sourceDensityMeasure,projectedMeasure_withDensity _ ha.continuous.measurable.ennreal_ofReal]
  congr 1
  funext z
  exact (sourceSchwartzFiber_density a hc ha hn θ z).symm

theorem schwartz_density_fourier (f : 𝓢(ℝ, ℝ)) (hf : ∀ z, 0 ≤ f z) (ξ : ℝ) :
    (𝓕 (complexSchwartz f)) ξ =
      sourceFourier (volume.withDensity (fun z => ENNReal.ofReal (f z))) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [sourceFourier,charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (hf z)]
  change Complex.exp _ * (f z : ℂ) = (f z : ℂ) * Complex.exp _
  rw [mul_comm]
  congr 2
  simp only [Real.inner_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

theorem sourceSchwartzFiber_fourier (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ ξ : ℝ) :
    (𝓕 (complexSchwartz (sourceSchwartzFiber a hc ha θ))) ξ =
      sourceFourier (sourceDensityMeasure a) (ξ • sourceNormal θ) := by
  let := sourceDensityMeasure_finite a hc ha.continuous hn
  rw [schwartz_density_fourier _ (sourceSchwartzFiber_nonneg a hc ha hn θ),
    ← sourceSchwartzFiber_measure a hc ha hn θ,source_fourier_slice]

theorem sourceSchwartzFiber_sliceEnergy (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x) (θ s : ℝ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
      (‖(𝓕 (complexSchwartz (sourceSchwartzFiber a hc ha θ))) ξ‖^2 * |ξ|^(s-1))) =
        sourceSliceEnergy (sourceDensityMeasure a) s θ := by
  simp_rw [sourceSchwartzFiber_fourier a hc ha hn θ]
  apply lintegral_congr
  intro ξ
  exact ENNReal.ofReal_mul (sq_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SmoothKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution

theorem sourceMollifier_nonneg (ε : ℝ) (hε : 0 < ε) (x : Plane) :
    0 ≤ sourceMollifier ε hε x := (sourceBump ε hε).nonneg_normed x

theorem sourceMollifier_smooth (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceMollifier ε hε) := (sourceBump ε hε).contDiff_normed

theorem sourceMollifier_compact (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (sourceMollifier ε hε) := (sourceBump ε hε).hasCompactSupport_normed

theorem sourceMollifier_support (ε : ℝ) (hε : 0 < ε) :
    Function.support (sourceMollifier ε hε) = ball (0 : Plane) ε :=
  (sourceBump ε hε).support_normed_eq

theorem sourceMollifier_integral (ε : ℝ) (hε : 0 < ε) :
    (∫ x, sourceMollifier ε hε x) = 1 := (sourceBump ε hε).integral_normed

instance sourceMollifier_probability (ε : ℝ) (hε : 0 < ε) :
    IsProbabilityMeasure (sourceDensityMeasure (sourceMollifier ε hε)) := by
  constructor
  rw [sourceDensityMeasure,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (f := sourceMollifier ε hε)
      ((sourceBump ε hε).integrable_normed (μ := volume))
      (Eventually.of_forall (sourceMollifier_nonneg ε hε)),sourceMollifier_integral]
  exact ENNReal.ofReal_one

theorem sourceMollifier_energy_le (α : Measure Plane) [IsFiniteMeasure α]
    (ε : ℝ) (hε : 0 < ε) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    rieszEnergy (α ∗ sourceDensityMeasure (sourceMollifier ε hε)) s ≤ rieszEnergy α s :=
  rieszEnergy_convolution_probability_le α _ hs hs2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SmoothConvolution
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal Convolution

theorem sourceSmoothDensity_nonneg (α : Measure Plane) (b : Plane → ℝ)
    (hb : ∀ y, 0 ≤ b y) (x : Plane) : 0 ≤ sourceSmoothDensity α b x :=
  integral_nonneg (fun _ => hb _)

theorem kernel_translate_integrable (α : Measure Plane) [IsFiniteMeasure α]
    (b : Plane → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (x : Plane) :
    Integrable (fun y => b (x-y)) α := by
  exact (hb.comp (by fun_prop)).integrable_of_hasCompactSupport
    (hc.comp_homeomorph (Homeomorph.subLeft x))

theorem sourceSmoothDensity_smooth (α : Measure Plane) [IsFiniteMeasure α]
    (b : Plane → ℝ) (hc : HasCompactSupport b) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceSmoothDensity α b) := by
  have h := contDiffOn_convolution_right_with_param_comp (μ := α)
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun x : Plane => x) contDiffOn_id isOpen_univ hc
    (g := fun _ : Plane => b) (fun _ _ _ hx => image_eq_zero_of_notMem_tsupport hx)
    (f := fun _ : Plane => (1 : ℝ)) continuous_const.locallyIntegrable
    (hb.comp contDiff_snd).contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [convolution,ContinuousLinearMap.mul_apply',one_mul,sourceSmoothDensity]

theorem sourceSmoothDensity_compact (α : Measure Plane) [IsFiniteMeasure α]
    (b : Plane → ℝ) (hc : HasCompactSupport b) {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ y ∂α, y ∈ K) : HasCompactSupport (sourceSmoothDensity α b) := by
  apply HasCompactSupport.intro (hK.add hc)
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hb
  exact hx ⟨y,hy,x-y,hb,by abel_nf⟩

theorem sourceSmoothDensity_measure (α : Measure Plane) [IsFiniteMeasure α]
    (b : Plane → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (hn : ∀ x, 0 ≤ b x) :
    α ∗ sourceDensityMeasure b = sourceDensityMeasure (sourceSmoothDensity α b) := by
  let := sourceDensityMeasure_finite b hc hb hn
  have hbm : Measurable b := hb.measurable
  have he (f : Plane → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x ∂(α ∗ sourceDensityMeasure b)) =
        ∫⁻ x, f x ∂sourceDensityMeasure (sourceSmoothDensity α b) := by
    rw [Measure.lintegral_conv hf]
    simp only [sourceDensityMeasure]
    have hinner (y : Plane) :
        (∫⁻ x, f (y+x) ∂volume.withDensity (fun x => ENNReal.ofReal (b x))) =
          ∫⁻ x, ENNReal.ofReal (b x) * f (y+x) :=
      lintegral_withDensity_eq_lintegral_mul _ hbm.ennreal_ofReal
        (hf.comp (measurable_const.add measurable_id))
    simp_rw [hinner]
    have hd (x : Plane) : ENNReal.ofReal (sourceSmoothDensity α b x) =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α :=
      ofReal_integral_eq_lintegral_ofReal (kernel_translate_integrable α b hc hb x)
        (Filter.Eventually.of_forall (fun _ => hn _))
    have hm : Measurable (fun p : Plane × Plane => ENNReal.ofReal (b (p.1-p.2))) := by fun_prop
    have hdm : Measurable (fun x => ENNReal.ofReal (sourceSmoothDensity α b x)) := by
      simp_rw [hd]
      exact hm.lintegral_prod_right'
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hf]
    have hmul (x : Plane) : (∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α) * f x =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) * f x ∂α :=
      (lintegral_mul_const _ (by fun_prop)).symm
    simp only [Pi.mul_apply]
    simp_rw [hd,hmul]
    conv_rhs => rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro y
    have ht := lintegral_add_left_eq_self (μ := (volume : Measure Plane))
      (fun x => ENNReal.ofReal (b (x-y)) * f x) y
    simpa only [add_sub_cancel_left] using ht
  exact Measure.ext_of_lintegral _ he

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectedDiameter
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceProjection_dist_le (θ : ℝ) (x y : Plane) :
    dist (sourceProjection θ x) (sourceProjection θ y) ≤ dist x y := by
  rw [Real.dist_eq,← sourceProjection_sub,dist_eq_norm]
  by_cases h : x-y = 0
  · simp [h,sourceProjection]
  · rw [abs_sourceProjection θ h]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)

theorem projectedMeasure_diameter (β : Measure Plane) [IsFiniteMeasure β]
    {D : ℝ} (hD : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D) (θ : ℝ) :
    ∀ᵐ z : ℝ × ℝ ∂(projectedMeasure β θ).prod (projectedMeasure β θ),
      dist z.1 z.2 ≤ D := by
  have hm : Measurable (sourceProjection θ) := by unfold sourceProjection; fun_prop
  rw [projectedMeasure,Measure.map_prod_map β β hm hm,
    ae_map_iff (hm.prodMap hm).aemeasurable (by measurability)]
  filter_upwards [hD] with z hz
  exact (sourceProjection_dist_le θ z.1 z.2).trans hz

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Graphs_SmoothFiberEstimate
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal SchwartzMap FourierTransform

theorem eLpNorm_nonneg_rpow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (eLpNorm' f p μ)^p = ∫⁻ x, (ENNReal.ofReal (f x))^p ∂μ := by
  rw [eLpNorm'_eq_lintegral_enorm,← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne',ENNReal.rpow_one]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hf x)]

theorem smooth_fiber_integral_bound (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure Plane) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D) (θ : ℝ) :
    (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2) *
      (∫⁻ z : ℝ, (projectedDensity (fun x => ENNReal.ofReal (a x)) θ z)^p
        ∂projectedMeasure β θ) ≤
      (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ) *
        (rieszEnergyOn (projectedMeasure β θ) t)^(1/2 : ℝ) *
        (sourceSliceEnergy (sourceDensityMeasure a) s θ)^(p/2) := by
  have h := source_fiber_lp_bound (projectedMeasure β θ)
    (sourceSchwartzFiber a hc ha θ) (sourceSchwartzFiber_nonneg a hc ha hn θ)
    hpq (by linarith) (by linarith) hD hupt (projectedMeasure_diameter β hdiam θ)
  rw [show 1-(2-s) = s-1 by ring,sourceSchwartzFiber_sliceEnergy a hc ha hn θ s] at h
  have hr := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ← ENNReal.rpow_mul,← ENNReal.rpow_mul,← ENNReal.rpow_mul,
    show (1/2:ℝ)*p = p/2 by ring,
    show (1/(2*p))*p = (1/2:ℝ) by field_simp [hpq.pos.ne'],
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hpq.nonneg,
    eLpNorm_nonneg_rpow _ _ (sourceSchwartzFiber_nonneg a hc ha hn θ) hpq.pos] at hr
  simpa only [sourceSchwartzFiber_density a hc ha hn θ,mul_assoc] using hr

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialDensity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceRadialUnit_ray (x : Plane) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    sourceRadialUnit x (x+r • sourceDirection θ) = sourceUnitDirection θ := by
  have hne : x+r • sourceDirection θ ≠ x := by
    intro h
    have hn := congrArg (fun y : Plane => ‖y-x‖) h
    simp only [add_sub_cancel_left,norm_smul,norm_sourceDirection,mul_one,sub_self,norm_zero,
      Real.norm_eq_abs,abs_of_pos hr] at hn
    exact hr.ne' hn
  apply Subtype.ext
  simp [sourceRadialUnit,sourceRadialVector,hne,sourceUnitDirection,norm_smul,
    norm_sourceDirection,Real.norm_eq_abs,abs_of_pos hr,smul_smul,hr.ne']

theorem translated_plane_polar_lintegral (f : Plane → ℝ≥0∞) (hf : Measurable f) (x : Plane) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ r in Ioi (0:ℝ),
      ENNReal.ofReal r * f (x+r • sourceDirection θ)) = ∫⁻ y : Plane, f y := by
  exact (plane_polar_lintegral (fun y => f (x+y)) (by fun_prop)).trans
    (lintegral_add_left_eq_self (μ := (volume : Measure Plane)) f x)

theorem sourceRadialUnit_withDensity (a : Plane → ℝ≥0∞) (ha : Measurable a) (x : Plane) :
    (volume.withDensity a).map (sourceRadialUnit x) =
      ((volume.restrict (Ioc 0 (2*Real.pi))).withDensity (sourceRadialDensity a x)).map
        sourceUnitDirection := by
  ext S hS
  rw [Measure.map_apply (measurable_sourceRadialUnit x) hS,
    Measure.map_apply continuous_sourceUnitDirection.measurable hS,
    withDensity_apply _ (hS.preimage (measurable_sourceRadialUnit x)),
    withDensity_apply _ (hS.preimage continuous_sourceUnitDirection.measurable)]
  let F : Plane → ℝ≥0∞ := (sourceRadialUnit x ⁻¹' S).indicator a
  have hF : Measurable F := ha.indicator (hS.preimage (measurable_sourceRadialUnit x))
  rw [← lintegral_indicator (hS.preimage (measurable_sourceRadialUnit x))]
  rw [← translated_plane_polar_lintegral F hF x]
  rw [← lintegral_indicator (hS.preimage continuous_sourceUnitDirection.measurable)]
  apply lintegral_congr
  intro θ
  by_cases hθ : sourceUnitDirection θ ∈ S
  · simp only [Set.indicator_of_mem (show θ ∈ sourceUnitDirection ⁻¹' S from hθ)]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hy : x+r • sourceDirection θ ∈ sourceRadialUnit x ⁻¹' S := by
      simpa only [mem_preimage,sourceRadialUnit_ray x θ hr] using hθ
    change _ * (sourceRadialUnit x ⁻¹' S).indicator a _ = _
    rw [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem (show θ ∉ sourceUnitDirection ⁻¹' S from hθ)]
    calc
      _ = ∫⁻ r in Ioi (0:ℝ), (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
        have hy : x+r • sourceDirection θ ∉ sourceRadialUnit x ⁻¹' S := by
          simpa only [mem_preimage,sourceRadialUnit_ray x θ hr] using hθ
        change _ * (sourceRadialUnit x ⁻¹' S).indicator a _ = 0
        rw [Set.indicator_of_notMem hy,mul_zero]
      _ = 0 := by simp

theorem sourceRadialDensity_le (a : Plane → ℝ≥0∞) (x : Plane) {D : ℝ}
    (hbound : ∀ y, a y ≠ 0 → dist y x ≤ D) (θ : ℝ) :
    sourceRadialDensity a x θ ≤ ENNReal.ofReal D * projectedDensity a θ (sourceProjection θ x) := by
  rw [projectedDensity_line]
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal D * a (x+r • sourceDirection θ) := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      change 0 < r at hr
      by_cases hz : a (x+r • sourceDirection θ) = 0
      · simp [hz]
      · apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        have h := hbound (x+r • sourceDirection θ) hz
        simpa [dist_eq_norm,norm_smul,norm_sourceDirection,Real.norm_eq_abs,abs_of_pos hr] using h
    _ = ENNReal.ofReal D * ∫⁻ r in Ioi (0:ℝ), a (x+r • sourceDirection θ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (lintegral_mono' Measure.restrict_le_self (le_refl _)) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_WeakApproximation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Convolution

theorem sourceMollifier_test_tendsto_at {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) (f : Plane → ℝ)
    (hf : Measurable f) (hc : ContinuousAt f 0) :
    Tendsto (fun n => ∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε n) (hε n)))
      atTop (𝓝 (f 0)) := by
  have ht : Tendsto (fun x : Plane => f (-x)) (𝓝 0) (𝓝 (f 0)) := by
    exact hc.tendsto.comp (by simpa only [neg_zero] using continuous_neg.tendsto (0 : Plane))
  have h := ContDiffBump.convolution_tendsto_right
    (μ := (volume : Measure Plane)) (φ := fun n => sourceBump (ε n) (hε n))
    (g := fun _ : ℕ => fun x : Plane => f (-x)) (k := fun _ => (0 : Plane))
    hlim (Eventually.of_forall (fun _ => (hf.comp measurable_neg).aestronglyMeasurable))
    (ht.comp tendsto_snd) tendsto_const_nhds
  have he (n : ℕ) : (∫ x, f x ∂sourceDensityMeasure (sourceMollifier (ε n) (hε n))) =
      ∫ x, sourceMollifier (ε n) (hε n) x • f x := by
    rw [sourceDensityMeasure,integral_withDensity_eq_integral_toReal_smul
      (sourceMollifier_smooth _ _).continuous.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (sourceMollifier_nonneg _ _ _)]
  simp_rw [he]
  simpa only [convolution,ContinuousLinearMap.lsmul_apply,zero_sub,neg_neg,sourceMollifier] using h

theorem sourceMollification_test_tendsto (α : Measure Plane) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (f : Plane → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C)
    (hc : ∀ᵐ y ∂α, ContinuousAt f y) :
    Tendsto (fun n => ∫ x, f x ∂(α ∗ sourceDensityMeasure (sourceMollifier (ε n) (hε n))))
      atTop (𝓝 (∫ x, f x ∂α)) := by
  let κ := fun n => sourceDensityMeasure (sourceMollifier (ε n) (hε n))
  have hi (n : ℕ) : Integrable f (α ∗ κ n) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)
  have hm (n : ℕ) : AEStronglyMeasurable (fun y => ∫ z, f (y+z) ∂κ n) α :=
    ((hf.comp measurable_add).aestronglyMeasurable).integral_prod_right'
  have hbound (n : ℕ) : ∀ᵐ y ∂α, ‖∫ z, f (y+z) ∂κ n‖ ≤ C := by
    filter_upwards with y
    simpa using norm_integral_le_of_norm_le_const (μ := κ n)
      (Eventually.of_forall (fun z => hb (y+z)))
  have hpoint : ∀ᵐ y ∂α, Tendsto (fun n => ∫ z, f (y+z) ∂κ n) atTop (𝓝 (f y)) := by
    filter_upwards [hc] with y hy
    have hcont : ContinuousAt (fun z : Plane => f (y+z)) 0 := by
      exact hy.comp_of_eq (continuous_const.add continuous_id).continuousAt (add_zero y)
    simpa only [add_zero] using sourceMollifier_test_tendsto_at hε hlim
      (fun z => f (y+z)) (hf.comp (measurable_const.add measurable_id)) hcont
  have h := tendsto_integral_of_dominated_convergence (fun _ => C) hm (integrable_const C) hbound hpoint
  have he (n : ℕ) : (∫ x, f x ∂(α ∗ κ n)) = ∫ y, ∫ z, f (y+z) ∂κ n ∂α := integral_conv (hi n)
  change Tendsto (fun n => ∫ x, f x ∂(α ∗ κ n)) atTop (𝓝 (∫ x, f x ∂α))
  simp_rw [he]
  exact h

theorem continuousAt_sourceRadialUnit (x y : Plane) (hy : y ≠ x) :
    ContinuousAt (sourceRadialUnit x) y := by
  rw [ContinuousAt,tendsto_subtype_rng]
  change ContinuousAt (sourceRadialVector x) y
  have hd : ContinuousAt (fun z : Plane => z-x) y := (continuous_id.sub continuous_const).continuousAt
  have h := (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd
  apply h.congr_of_eventuallyEq
  have hne : ∀ᶠ z in 𝓝 y, z ≠ x := isClosed_singleton.isOpen_compl.mem_nhds hy
  filter_upwards [hne] with z hz
  simp [sourceRadialVector,hz]

theorem sourceMollification_radial_test_tendsto (α : Measure Plane) [IsFiniteMeasure α]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    (x : Plane) (hx : ∀ᵐ y ∂α, y ≠ x) (F : BoundedContinuousFunction UnitCircle ℝ) :
    Tendsto (fun n => ∫ ω, F ω ∂(α ∗ sourceDensityMeasure (sourceMollifier (ε n) (hε n))).map
      (sourceRadialUnit x)) atTop (𝓝 (∫ ω, F ω ∂α.map (sourceRadialUnit x))) := by
  simp_rw [integral_map (measurable_sourceRadialUnit x).aemeasurable F.continuous.aestronglyMeasurable]
  exact sourceMollification_test_tendsto α hε hlim (fun y => F (sourceRadialUnit x y))
    (F.continuous.measurable.comp (measurable_sourceRadialUnit x))
    (fun y => F.norm_coe_le_norm _) (hx.mono (fun y hy =>
      F.continuous.continuousAt.comp (continuousAt_sourceRadialUnit x y hy)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionMoment
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measure_power_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {r q : ℝ}
    (hrq : r.HolderConjugate q) :
    (∫⁻ x, F x ∂μ)^r ≤ (μ univ)^(r-1) * (∫⁻ x, (F x)^r ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hrq hF.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
  have hh := ENNReal.rpow_le_rpow h hrq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hrq.nonneg,← ENNReal.rpow_mul,
    one_div_mul_cancel hrq.pos.ne',ENNReal.rpow_one,← ENNReal.rpow_mul] at hh
  have hq : (1/q)*r = r-1 := by
    rw [show (1/q)*r = r/q by ring]
    exact (div_eq_iff hrq.symm.pos.ne').mpr hrq.sub_one_mul_conj.symm
  rw [hq] at hh
  simpa only [mul_comm] using hh

theorem projection_energy_moment (μ : Measure Plane) [IsFiniteMeasure μ]
    {t r : ℝ} (ht : 0 < t) (hr : 1 < r) (htr : t*r < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (rieszEnergyOn (projectedMeasure μ θ) t)^r) ≤
      angularEnergyConstant (t*r) * (rieszEnergy μ t)^r := by
  let ρ := differenceEnergyMeasure μ t
  let : SFinite ρ := by dsimp [ρ,differenceEnergyMeasure]; infer_instance
  let F : ℝ → Plane × Plane → ℝ≥0∞ := fun θ z => sineKernel t (θ-planePhase (z.1-z.2))
  have hF : Measurable (fun z : ℝ × (Plane × Plane) => F z.1 z.2) := by
    dsimp [F,sineKernel,planePhase]
    fun_prop
  have hrq := Real.HolderConjugate.conjExponent hr
  have hmean (θ : ℝ) : (rieszEnergyOn (projectedMeasure μ θ) t)^r ≤
      (ρ univ)^(r-1) * ∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ := by
    rw [projected_energy_weighted_formula μ ht]
    have hmθ : Measurable (F θ) := by dsimp [F,sineKernel,planePhase]; fun_prop
    exact measure_power_mean ρ (F θ) hmθ hrq
  have hsin (θ : ℝ) (z : Plane × Plane) :
      (F θ z)^r = sineKernel (t*r) (θ-planePhase (z.1-z.2)) := by
    dsimp [F,sineKernel]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hint : (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), ∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ) =
      angularEnergyConstant (t*r) * ρ univ := by
    rw [lintegral_lintegral_swap (hF.pow_const r).aemeasurable]
    simp_rw [hsin,sineKernel_shift_integral (mul_pos ht (zero_lt_one.trans hr)) htr]
    exact lintegral_const _
  calc
    _ ≤ ∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (ρ univ)^(r-1) *
        (∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ) := lintegral_mono hmean
    _ = (ρ univ)^(r-1) * (angularEnergyConstant (t*r) * ρ univ) := by
      rw [lintegral_const_mul _ (by fun_prop),hint]
    _ = angularEnergyConstant (t*r) * (ρ univ)^r := by
      have hp := ENNReal.rpow_add_of_nonneg (x := ρ univ) (r-1) 1 (by linarith) zero_le_one
      rw [sub_add_cancel,ENNReal.rpow_one] at hp
      rw [hp]
      ac_rfl
    _ = _ := by dsimp only [ρ]; rw [differenceEnergyMeasure_mass,rieszEnergyOn_plane]

theorem measurable_projected_energy (μ : Measure Plane) [IsFiniteMeasure μ] (t : ℝ) :
    Measurable (fun θ => rieszEnergyOn (projectedMeasure μ θ) t) := by
  simp_rw [projected_energy_formula]
  have hm : Measurable (fun p : ℝ × (Plane × Plane) =>
      (ENNReal.ofReal |sourceProjection p.1 (p.2.1-p.2.2)|)^(-t)) := by
    unfold sourceProjection
    fun_prop
  exact hm.lintegral_prod_right

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialMixedEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem radial_angular_holder (E S : ℝ → ℝ≥0∞) (hE : Measurable E) (hS : Measurable S)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ θ in Ioc 0 (2*Real.pi), (E θ)^(1/2:ℝ) * (S θ)^(p/2)) ≤
      (∫⁻ θ in Ioc 0 (2*Real.pi), (E θ)^(1/(2-p)))^((2-p)/2) *
        (∫⁻ θ in Ioc 0 (2*Real.pi), S θ)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hc : (2/(2-p)).HolderConjugate (2/p) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ hd).mpr (by linarith)
    · simp only [inv_div]
      ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioc 0 (2*Real.pi))) hc
    (hE.pow_const (1/2:ℝ)).aemeasurable (hS.pow_const (p/2)).aemeasurable
  simp only [Pi.mul_apply,← ENNReal.rpow_mul] at h
  have h₁ : (1/2:ℝ)*(2/(2-p)) = 1/(2-p) := by ring
  have h₂ : (p/2)*(2/p) = 1 := by field_simp
  have h₃ : 1/(2/(2-p)) = (2-p)/2 := by field_simp
  have h₄ : 1/(2/p) = p/2 := by field_simp
  simpa only [h₁,h₂,h₃,h₄,ENNReal.rpow_one] using h

theorem radial_mixed_energy_bound (α β : Measure Plane) [IsFiniteMeasure α]
    [IsFiniteMeasure β] {s t p : ℝ} (hs : 0 < s) (hs2 : s < 2) (ht : 0 < t)
    (hp1 : 1 < p) (hp2 : p < 2) (htr : t/(2-p) < 1) :
    (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (∫⁻ θ in Ioc 0 (2*Real.pi),
        (rieszEnergyOn (projectedMeasure β θ) t)^(1/2:ℝ) * (sourceSliceEnergy α s θ)^(p/2)) ≤
      (angularEnergyConstant (t/(2-p)))^((2-p)/2) *
        (rieszEnergy β t)^(1/2:ℝ) * (2 * rieszEnergy α s)^(p/2) := by
  have hp : 0 < p := by linarith
  have hd : 0 < 2-p := by linarith
  have hr : 1 < 1/(2-p) := (lt_div_iff₀ hd).mpr (by linarith)
  have hh := radial_angular_holder _ _ (measurable_projected_energy β t)
    (measurable_sourceSliceEnergy α s) hp1 hp2
  have hm := projection_energy_moment β ht hr (by simpa [div_eq_mul_inv] using htr)
  have hpow := ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ (2-p)/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (2-p)/2),
    ← ENNReal.rpow_mul] at hpow
  have hx : (1/(2-p))*((2-p)/2) = (1/2:ℝ) := by field_simp
  rw [hx,show t*(1/(2-p)) = t/(2-p) by ring] at hpow
  have h := mul_le_mul_right (hh.trans (mul_le_mul_left hpow _))
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2))
  calc
    _ ≤ _ := h
    _ = (angularEnergyConstant (t/(2-p)))^((2-p)/2) *
        (rieszEnergy β t)^(1/2:ℝ) *
        ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
          (∫⁻ θ in Ioc 0 (2*Real.pi), sourceSliceEnergy α s θ)^(p/2)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p/2),
        source_slice_average_energy α hs hs2]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTonelli
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem radial_density_integral_le_fibers (a : Plane → ℝ≥0∞) (ha : Measurable a)
    (β : Measure Plane) [IsFiniteMeasure β] {D p : ℝ} (hp : 0 ≤ p)
    (hbound : ∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) :
    (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi), (sourceRadialDensity a x θ)^p) ∂β) ≤
      (ENNReal.ofReal D)^p *
        ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ z, (projectedDensity a θ z)^p
          ∂projectedMeasure β θ := by
  have hm : Measurable (fun v : Plane × ℝ =>
      (projectedDensity a v.2 (sourceProjection v.2 v.1))^p) := by
    have hc : Continuous (fun v : Plane × ℝ => (v.2,sourceProjection v.2 v.1)) := by
      unfold sourceProjection
      fun_prop
    exact ((measurable_projectedDensity_joint a ha).comp hc.measurable).pow_const p
  calc
    _ ≤ ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (ENNReal.ofReal D)^p * (projectedDensity a θ (sourceProjection θ x))^p) ∂β := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      apply lintegral_mono
      intro θ
      have h := ENNReal.rpow_le_rpow (sourceRadialDensity_le a x hx θ) hp
      rwa [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
    _ = ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ x,
        (ENNReal.ofReal D)^p * (projectedDensity a θ (sourceProjection θ x))^p ∂β :=
      lintegral_lintegral_swap (measurable_const.mul hm).aemeasurable
    _ = (ENNReal.ofReal D)^p *
        ∫⁻ θ in Ioc 0 (2*Real.pi), ∫⁻ x,
          (projectedDensity a θ (sourceProjection θ x))^p ∂β := by
      simp_rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro θ
      exact (lintegral_map ((measurable_projectedDensity a ha θ).pow_const p)
        (by unfold sourceProjection; fun_prop)).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_SmoothRadialEstimate
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.sourceMollifier_probability _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem smooth_radial_density_energy_bound (a : Plane → ℝ) (hc : HasCompactSupport a)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure Plane) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y, a y ≠ 0 → dist y x ≤ D) :
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)) *
      (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal (a y)) x θ)^p) ∂β) ≤
      ((ENNReal.ofReal D)^p * (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ)) *
        ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
          (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy (sourceDensityMeasure a) s)^(p/2)) := by
  let := sourceDensityMeasure_finite a hc ha.continuous hn
  let c₁ := (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)
  let c₂ := (ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2)
  let d := (ENNReal.ofReal (D^(t-(2-s)*p)))^(1/2 : ℝ)
  let F := fun θ => ∫⁻ z, (projectedDensity (fun y => ENNReal.ofReal (a y)) θ z)^p
    ∂projectedMeasure β θ
  let M := fun θ => (rieszEnergyOn (projectedMeasure β θ) t)^(1/2 : ℝ) *
    (sourceSliceEnergy (sourceDensityMeasure a) s θ)^(p/2)
  have hc₁ : c₁ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith [hpq.pos]) ENNReal.ofReal_ne_top
  have hd : d ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hf : c₁ * (∫⁻ θ in Ioc 0 (2*Real.pi), F θ) ≤
      d * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ := by
    rw [← lintegral_const_mul' _ _ hc₁,← lintegral_const_mul' _ _ hd]
    apply lintegral_mono
    intro θ
    exact (smooth_fiber_integral_bound a hc ha hn β hpq hs1 hs2 hD hupt hdiam θ).trans_eq
      (by dsimp [d,M]; ac_rfl)
  have hr := radial_density_integral_le_fibers (fun y => ENNReal.ofReal (a y))
    ha.continuous.measurable.ennreal_ofReal β hpq.nonneg
    (hbound.mono (fun x hx y hy => hx y (by intro h; exact hy (by simp [h]))))
  have ht : 0 < t := (mul_pos (by linarith : 0 < 2-s) hpq.pos).trans hupt
  have hm := radial_mixed_energy_bound (sourceDensityMeasure a) β (by linarith) hs2 ht
    (Real.holderConjugate_iff.mp hpq).1 hp2 ((div_lt_one (by linarith : 0 < 2-p)).mpr htp)
  calc
    _ ≤ (c₂*c₁) * ((ENNReal.ofReal D)^p * ∫⁻ θ in Ioc 0 (2*Real.pi), F θ) :=
      mul_le_mul_right hr _
    _ = ((ENNReal.ofReal D)^p*c₂) * (c₁ * ∫⁻ θ in Ioc 0 (2*Real.pi), F θ) := by ac_rfl
    _ ≤ ((ENNReal.ofReal D)^p*c₂) * (d * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ) :=
      mul_le_mul_right hf _
    _ = ((ENNReal.ofReal D)^p*d) * (c₂ * ∫⁻ θ in Ioc 0 (2*Real.pi), M θ) := by ac_rfl
    _ ≤ _ := mul_le_mul_right hm _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_MollifiedRadialBound
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Metric
open scoped ENNReal NNReal

theorem sourceMollification_support_bound (α : Measure Plane) [IsFiniteMeasure α]
    {K : Set Plane} (hα : ∀ᵐ z ∂α, z ∈ K) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : Plane) {D : ℝ} (hD : ∀ z ∈ K, dist z x ≤ D) :
    ∀ y, sourceSmoothDensity α (sourceMollifier ε hε) y ≠ 0 → dist y x ≤ D+1 := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with z hz
  by_contra hb
  have hm : y-z ∈ ball (0 : Plane) ε := by
    rw [← sourceMollifier_support ε hε]
    exact hb
  have hd : dist y z < ε := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hm
  exact h ((dist_triangle y z x).trans ((add_le_add hd.le (hD z hz)).trans
    (by simpa only [add_comm] using add_le_add_right hε1 D)))

theorem mollified_radial_density_energy_bound (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)) *
      (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal
          (sourceSmoothDensity α (sourceMollifier ε hε) y)) x θ)^p) ∂β) ≤
      ((ENNReal.ofReal (D+1))^p * (ENNReal.ofReal ((D+1)^(t-(2-s)*p)))^(1/2 : ℝ)) *
        ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
          (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy α s)^(p/2)) := by
  let b := sourceMollifier ε hε
  have hc := sourceMollifier_compact ε hε
  have hb := sourceMollifier_smooth ε hε
  have hn := sourceMollifier_nonneg ε hε
  have h := smooth_radial_density_energy_bound (sourceSmoothDensity α b)
    (sourceSmoothDensity_compact α b hc hK hα) (sourceSmoothDensity_smooth α b hc hb)
    (sourceSmoothDensity_nonneg α b hn) β hpq hp2 hs1 hs2 (by linarith only [hD] : 0 < D+1)
    hupt htp (hdiam.mono (fun z hz => by linarith only [hz]))
    (hbound.mono (fun x hx => sourceMollification_support_bound α hα ε hε hε1 x hx))
  have he : rieszEnergy (sourceDensityMeasure (sourceSmoothDensity α b)) s ≤ rieszEnergy α s := by
    rw [← sourceSmoothDensity_measure α b hc hb.continuous hn]
    exact sourceMollifier_energy_le α ε hε (by linarith only [hs1]) hs2
  apply h.trans
  apply mul_le_mul_right
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow _ (div_nonneg hpq.pos.le (by norm_num) : 0 ≤ p/2)
  exact mul_le_mul_right he 2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestBound
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem sourceTestNorm_angular_density_le (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    sourceTestNorm q (((volume.restrict (Ioc 0 (2*Real.pi))).withDensity g).map
      sourceUnitDirection) ≤
        (∫⁻ θ in Ioc 0 (2*Real.pi), (g θ)^p)^(1/p) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  let ν : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  let G : ℝ → ℝ≥0∞ := fun θ => ‖F (sourceUnitDirection θ)‖ₑ
  have hFc : Continuous (F ∘ sourceUnitDirection) :=
    F.continuous.comp continuous_sourceUnitDirection
  have hG : Measurable G := hFc.enorm.measurable
  have hq : (∫⁻ θ, (G θ)^q ∂ν)^(1/q) ≤ 1 := by
    rw [sourceArcLength,eLpNorm_map_measure F.continuous.aestronglyMeasurable
      continuous_sourceUnitDirection.measurable.aemeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
        ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.symm.nonneg] at hF
    simpa only [Function.comp_apply,G,ν] using hF
  have hb := enorm_integral_le_lintegral_enorm
    (μ := (ν.withDensity g).map sourceUnitDirection) (fun ω => F ω)
  rw [← ofReal_norm,lintegral_map (by fun_prop) continuous_sourceUnitDirection.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hg hG] at hb
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.aemeasurable hG.aemeasurable
  have hh' : (∫⁻ θ, g θ * G θ ∂ν) ≤ (∫⁻ θ, (g θ)^p ∂ν)^(1/p) := by
    exact hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _))
  exact hb.trans hh'

theorem sourceTestNorm_radial_density_rpow_le (a : Plane → ℝ≥0∞) (ha : Measurable a)
    {p q : ℝ} (hpq : p.HolderConjugate q) (x : Plane) :
    (sourceTestNorm q ((volume.withDensity a).map (sourceRadialUnit x)))^p ≤
      ∫⁻ θ in Ioc 0 (2*Real.pi), (sourceRadialDensity a x θ)^p := by
  rw [sourceRadialUnit_withDensity a ha x]
  have h := ENNReal.rpow_le_rpow (sourceTestNorm_angular_density_le
    (sourceRadialDensity a x) (measurable_sourceRadialDensity a ha x) hpq) hpq.nonneg
  rwa [← ENNReal.rpow_mul,one_div_mul_cancel hpq.pos.ne',ENNReal.rpow_one] at h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialFatou
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_rpow_le_liminf (γ : Measure UnitCircle) (γn : ℕ → Measure UnitCircle)
    {p q : ℝ} (hp : 0 < p) (A : ℕ → ℝ≥0∞)
    (hγ : ∀ F : BoundedContinuousFunction UnitCircle ℝ,
      Tendsto (fun n => ∫ ω, F ω ∂γn n) atTop (𝓝 (∫ ω, F ω ∂γ)))
    (hA : ∀ n, (sourceTestNorm q (γn n))^p ≤ A n) :
    (sourceTestNorm q γ)^p ≤ liminf A atTop := by
  have he : (sourceTestNorm q γ)^p =
      ⨆ (F : BoundedContinuousFunction UnitCircle ℝ)
        (_ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1),
          (ENNReal.ofReal ‖∫ ω, F ω ∂γ‖)^p := by
    change (ENNReal.orderIsoRpow p hp) (⨆ (F : BoundedContinuousFunction UnitCircle ℝ), ⨆ _ : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ 1,
      ENNReal.ofReal ‖∫ ω, F ω ∂γ‖) = _
    rw [OrderIso.map_iSup]
    congr 1
    funext F
    exact (ENNReal.orderIsoRpow p hp).map_iSup _
  rw [he]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have ht := ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp
    ((ENNReal.continuous_ofReal.tendsto _).comp (hγ F).norm)
  have hle (n : ℕ) : ENNReal.ofReal ‖∫ ω, F ω ∂γn n‖ ≤ sourceTestNorm q (γn n) :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (fun n =>
    (ENNReal.rpow_le_rpow (hle n) hp.le).trans (hA n)))

theorem radial_testNorm_fatou (α β : Measure Plane) [IsFiniteMeasure α] [IsFiniteMeasure β]
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x) :
    (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) ≤
      liminf (fun n => ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal
          (sourceSmoothDensity α (sourceMollifier (ε n) (hε n)) y)) x θ)^p) ∂β) atTop := by
  let a := fun n => sourceSmoothDensity α (sourceMollifier (ε n) (hε n))
  let A := fun n (x : Plane) => ∫⁻ θ in Ioc 0 (2*Real.pi),
    (sourceRadialDensity (fun y => ENNReal.ofReal (a n y)) x θ)^p
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) := sourceSmoothDensity_smooth α _
    (sourceMollifier_compact _ _) (sourceMollifier_smooth _ _)
  have hm (n : ℕ) : Measurable (A n) :=
    ((measurable_sourceRadialDensity_joint _ (ha n).continuous.measurable.ennreal_ofReal).pow_const p).lintegral_prod_right'
  have hpoint : ∀ᵐ x ∂β, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ≤
      liminf (fun n => A n x) atTop := by
    filter_upwards [hx] with x hx
    apply sourceTestNorm_rpow_le_liminf _ _ hpq.pos (fun n => A n x)
      (sourceMollification_radial_test_tendsto α hε hlim x hx)
    intro n
    have he := sourceSmoothDensity_measure α (sourceMollifier (ε n) (hε n))
      (sourceMollifier_compact (ε n) (hε n))
      (sourceMollifier_smooth (ε n) (hε n)).continuous (sourceMollifier_nonneg (ε n) (hε n))
    rw [he]
    exact sourceTestNorm_radial_density_rpow_le _ (ha n).continuous.measurable.ennreal_ofReal hpq x
  exact (lintegral_mono_ae hpoint).trans (lintegral_liminf_le hm)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem radialEnergyPrefactor_pos {s p : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    0 < radialEnergyPrefactor s p := by
  have h₁ := sourceEnergyConstant_pos (by linarith : 0 < 2-s) (by linarith : 2-s < 1)
  have h₂ := sourceEnergyConstant_pos (by linarith : 0 < s) hs2
  unfold radialEnergyPrefactor
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr h₂) ENNReal.ofReal_ne_top).ne'
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr h₁) ENNReal.ofReal_ne_top).ne')

theorem radialEnergyPrefactor_ne_top {s p : ℝ} (hp : 0 ≤ p) :
    radialEnergyPrefactor s p ≠ ∞ := by
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

theorem radial_testNorm_energy_bound (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x) :
    radialEnergyPrefactor s p *
      (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) ≤
        radialEnergyMajorant α β D s t p := by
  let ε := fun n : ℕ => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let J := fun n => ∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
    (sourceRadialDensity (fun y => ENNReal.ofReal
      (sourceSmoothDensity α (sourceMollifier (ε n) (hε n)) y)) x θ)^p) ∂β
  let c := radialEnergyPrefactor s p
  let R := radialEnergyMajorant α β D s t p
  have hc0 : c ≠ 0 := (radialEnergyPrefactor_pos hs1 hs2).ne'
  have hct : c ≠ ∞ := radialEnergyPrefactor_ne_top hpq.nonneg
  have hJ (n : ℕ) : c * J n ≤ R :=
    mollified_radial_density_energy_bound α β hK hα hpq hp2 hs1 hs2 hD hupt htp
      hdiam hbound (ε n) (hε n) (hε1 n)
  have hJ' (n : ℕ) : J n ≤ c⁻¹ * R := by
    calc
      J n = c⁻¹*(c*J n) := by rw [← mul_assoc,ENNReal.inv_mul_cancel hc0 hct,one_mul]
      _ ≤ _ := mul_le_mul_right (hJ n) _
  have hl : liminf J atTop ≤ c⁻¹*R := by
    have h := liminf_le_liminf (f := atTop) (Eventually.of_forall hJ')
    simpa only [liminf_const] using h
  have hf := radial_testNorm_fatou α β hε hlim hpq hx
  calc
    _ ≤ c*(c⁻¹*R) := mul_le_mul_right (hf.trans hl) c
    _ = R := by rw [← mul_assoc,ENNReal.mul_inv_cancel hc0 hct,one_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_FiniteRadialTestEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem radialEnergyMajorant_lt_top (α β : Measure Plane) {D s t p : ℝ}
    (hp : 0 < p) (hp2 : p < 2) (ht : 0 < t) (htp : t < 2-p)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    radialEnergyMajorant α β D s t p < ∞ := by
  unfold radialEnergyMajorant
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by linarith)
          (angularEnergyConstant_lt_top (div_pos ht (sub_pos.mpr hp2))
            ((div_lt_one (sub_pos.mpr hp2)).mpr htp)).ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hβ.ne)
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_lt_top (by norm_num) hα).ne

theorem finite_radial_testNorm_integral_oai (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hαK : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) < ∞ := by
  have hb := radial_testNorm_energy_bound α β hK hαK hpq hp2 hs1 hs2 hD hupt htp
    hdiam hbound hx
  have ht : 0 < t := (mul_pos (by linarith : 0 < 2-s) hpq.pos).trans hupt
  have hR := radialEnergyMajorant_lt_top α β (D := D) hpq.pos hp2 ht htp hα hβ
  by_contra h
  have he : (∫⁻ x, (sourceTestNorm q (α.map (sourceRadialUnit x)))^p ∂β) = ∞ :=
    top_unique (not_lt.mp h)
  rw [he,ENNReal.mul_top (radialEnergyPrefactor_pos hs1 hs2).ne'] at hb
  exact (not_le_of_gt hR) hb

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.finite_radial_testNorm_integral_oai := @OAI.PlanarFalconer.finite_radial_testNorm_integral_oai
