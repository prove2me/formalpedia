-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:20:17.933188+00:00
-- url     : https://prove2.me/submissions/cfdce9e4-f4d1-41fa-aefa-adce223ede52

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalCandidate_L2_of_bounds
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalLeading_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalResidual_heatBound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_leading_time_primitive

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.clip_of_mem _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.clip_of_not_mem _root_.OAI.TamingCompatibility.GeometricHilbert.KernelSeries.term_outside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

lemma weight_pos (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < weight N t x y := lt_of_lt_of_le zero_lt_one (weight_one_le N ht x y)

lemma weight_submultiplicative (N : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x z y : X) : weight N (t+s) x y ≤ weight N t x z * weight N s z y := by
  rw [weight, weight, weight, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hT : 0 < Real.sqrt (t+s) := Real.sqrt_pos.2 (add_pos ht hs)
  have h1 := div_le_div_of_nonneg_left (dist_nonneg (x := x) (y := z))
    (Real.sqrt_pos.2 ht) (Real.sqrt_le_sqrt (le_add_of_nonneg_right hs.le))
  have h2 := div_le_div_of_nonneg_left (dist_nonneg (x := z) (y := y))
    (Real.sqrt_pos.2 hs) (Real.sqrt_le_sqrt (le_add_of_nonneg_left ht.le))
  have hd := div_le_div_of_nonneg_right (dist_triangle x z y) hT.le
  rw [add_div] at hd
  have hmul : 0 ≤ (dist x z / Real.sqrt t) * (dist z y / Real.sqrt s) := by positivity
  nlinarith

lemma weight_continuous (N : ℕ) (t : ℝ) (x : X) : Continuous (weight N t x) := by
  unfold weight
  fun_prop

variable [MeasurableSpace X] [NormedRing B] [NormedAlgebra ℝ B]

lemma spatial_convolution_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hA : 0 ≤ A)
    (K L : X → X → B) (x y : X)
    (hK : ∀ z, weight N t x z * ‖K x z‖ ≤ A)
    (hL : Integrable (fun z => weight N s z y * ‖L z y‖) μ)
    (hLI : (∫ z, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      A * (weight N s z y * ‖L z y‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N t x z * ‖K x z‖) * (weight N s z y * ‖L z y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hK z)
        (mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hL.const_mul (A / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      A * (weight N s z y * ‖L z y‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, A * (weight N s z y * ‖L z y‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hL.const_mul _) hpoint
    _ = A * (∫ z, weight N s z y * ‖L z y‖ ∂μ) := integral_const_mul _ _
    _ ≤ A*C := mul_le_mul_of_nonneg_left hLI hA

lemma spatial_convolution_bound_right (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C)
    (K L : X → X → B) (x y : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : ∀ z, weight N s z y * ‖L z y‖ ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K x z * L z y) μ) :
    Integrable (fun z => K x z * L z y) μ ∧
      weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ≤ A*C := by
  have hw := weight_pos N (add_pos ht hs) x y
  have hpoint (z : X) : weight N (t+s) x y * ‖K x z * L z y‖ ≤
      C * (weight N t x z * ‖K x z‖) := by
    calc
      _ ≤ (weight N t x z * weight N s z y) * (‖K x z‖*‖L z y‖) :=
        mul_le_mul (weight_submultiplicative N ht hs x z y) (norm_mul_le _ _)
          (norm_nonneg _) (mul_nonneg (weight_pos N ht x z).le (weight_pos N hs z y).le)
      _ = (weight N s z y * ‖L z y‖) * (weight N t x z * ‖K x z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hL z)
        (mul_nonneg (weight_pos N ht x z).le (norm_nonneg _))
  have hint : Integrable (fun z => K x z * L z y) μ := by
    apply (hK.const_mul (C / weight N (t+s) x y)).mono' hprod
    filter_upwards [] with z
    have h := (le_div_iff₀ hw).mpr (show ‖K x z * L z y‖ * weight N (t+s) x y ≤
      C * (weight N t x z * ‖K x z‖) by simpa only [mul_comm] using hpoint z)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ weight N (t+s) x y * (∫ z, ‖K x z * L z y‖ ∂μ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ z, weight N (t+s) x y * ‖K x z * L z y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ z, C * (weight N t x z * ‖K x z‖) ∂μ :=
      integral_mono (hint.norm.const_mul _) (hK.const_mul _) hpoint
    _ = C * (∫ z, weight N t x z * ‖K x z‖ ∂μ) := integral_const_mul _ _
    _ ≤ C*A := mul_le_mul_of_nonneg_left hKI hC
    _ = A*C := mul_comm _ _

lemma time_integrand_bound (μ : Measure X) (N : ℕ) {t s A C : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hst : s < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ) :
    Integrable (fun z => K (t-s) x z * L s z y) μ ∧
      weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t^2 := by
  have hts : 0 < t-s := sub_pos.mpr hst
  have hleft := spatial_convolution_bound μ N hts hs (by positivity : 0 ≤ A/(t-s)^2)
    (K (t-s)) (L s) x y hKsup hL hLI hprod
  refine ⟨hleft.1, ?_⟩
  by_cases hhalf : s ≤ t/2
  · have hden : t^2/4 ≤ (t-s)^2 := by nlinarith [sq_nonneg (t/2-s)]
    have hdiv : A/(t-s)^2 ≤ 4*A/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hts) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hden)]
    calc
      _ ≤ (A/(t-s)^2)*C := by simpa using hleft.2
      _ ≤ (4*A/t^2)*C := mul_le_mul_of_nonneg_right hdiv hC
      _ = _ := by ring
  · have hden : t^2/4 ≤ s^2 := by nlinarith [sq_nonneg (s-t/2)]
    have hdiv : C/s^2 ≤ 4*C/t^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ht)).2
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hden)]
    have hright := spatial_convolution_bound_right μ N hts hs
      (by positivity : 0 ≤ C/s^2) (K (t-s)) (L s) x y hK hKI hLsup hprod
    calc
      _ ≤ A*(C/s^2) := by simpa using hright.2
      _ ≤ A*(4*C/t^2) := mul_le_mul_of_nonneg_left hdiv hA
      _ = _ := by ring

lemma time_convolution_bound (μ : Measure X) (N : ℕ) {t A C : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (K L : ℝ → X → X → B) (x y : X)
    (hKsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N (t-s) x z * ‖K (t-s) x z‖ ≤ A/(t-s)^2)
    (hLsup : ∀ s ∈ Ioo 0 t, ∀ z, weight N s z y * ‖L s z y‖ ≤ C/s^2)
    (hK : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N (t-s) x z * ‖K (t-s) x z‖) μ)
    (hL : ∀ s ∈ Ioo 0 t, Integrable (fun z => weight N s z y * ‖L s z y‖) μ)
    (hKI : ∀ s ∈ Ioo 0 t, (∫ z, weight N (t-s) x z * ‖K (t-s) x z‖ ∂μ) ≤ A)
    (hLI : ∀ s ∈ Ioo 0 t, (∫ z, weight N s z y * ‖L s z y‖ ∂μ) ≤ C)
    (hprod : ∀ s ∈ Ioo 0 t, AEStronglyMeasurable (fun z => K (t-s) x z * L s z y) μ)
    (htime : AEStronglyMeasurable (fun s => ∫ z, K (t-s) x z * L s z y ∂μ)
      (volume.restrict (Ioo 0 t))) :
    IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) ∧
      weight N t x y * ‖∫ s in Ioo 0 t, ∫ z, K (t-s) x z * L s z y ∂μ‖ ≤ 4*A*C/t := by
  have hw := weight_pos N ht x y
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 t) := (time_integrand_bound μ N ht hs.1 hs.2
    hA hC K L x y (hKsup s hs) (hLsup s hs) (hK s hs) (hL s hs)
    (hKI s hs) (hLI s hs) (hprod s hs)).2
  have hi : IntegrableOn (fun s => ∫ z, K (t-s) x z * L s z y ∂μ) (Ioo 0 t) := by
    apply (integrableOn_const (C := 4*A*C/t^2/weight N t x y)
      (hs := measure_Ioo_lt_top.ne)).mono' htime
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (le_div_iff₀ hw).2
    simpa only [mul_comm] using hpoint s hs
  refine ⟨hi, ?_⟩
  calc
    _ ≤ weight N t x y * (∫ s in Ioo 0 t, ‖∫ z, K (t-s) x z * L s z y ∂μ‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hw.le
    _ = ∫ s in Ioo 0 t, weight N t x y * ‖∫ z, K (t-s) x z * L s z y ∂μ‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ _s in Ioo 0 t, 4*A*C/t^2 := by
      apply integral_mono_ae (hi.norm.const_mul _)
        (integrableOn_const (hs := measure_Ioo_lt_top.ne))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hpoint s hs
    _ = 4*A*C/t := by
      simp only [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioo_of_le ht.le,
        smul_eq_mul, sub_zero]
      field_simp

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurIntegration
open _root_.MeasureTheory
variable {X Y B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
variable (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma product_integrable {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    Integrable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : X × Y => f p.1 * g p.1 p.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => (hgi x).const_mul (f x)), ?_⟩
  have hi (x : X) : (∫ y, ‖f x*g x y‖ ∂ν) = f x * ∫ y, g x y ∂ν := by
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (hg0 x _))]
    exact integral_const_mul _ _
  simp_rw [hi]
  apply (hf.mul_const C).mono'
    (by simpa only [hi] using hm.norm.integral_prod_right')
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (mul_nonneg (hf0 x) (integral_nonneg (hg0 x)))]
    exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

omit [SFinite μ] in
lemma product_integral_le {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C) :
    (∫ x, ∫ y, f x*g x y ∂ν ∂μ) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  rw [mul_comm C, ← integral_mul_const]
  apply integral_mono hi.integral_prod_left (hf.mul_const C)
  intro x
  change (∫ y, f x*g x y ∂ν) ≤ f x*C
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (hf0 x)

lemma norm_integral_row {f : X → ℝ} {g : X → Y → ℝ} {C : ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hg : StronglyMeasurable (Function.uncurry g)) (hg0 : ∀ x y, 0 ≤ g x y)
    (hgi : ∀ x, Integrable (g x) ν) (hC : ∀ x, (∫ y, g x y ∂ν) ≤ C)
    (H : X → Y → B) (hH : StronglyMeasurable (Function.uncurry H))
    (hdom : ∀ x y, ‖H x y‖ ≤ f x*g x y) :
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
      (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ C * ∫ x, f x ∂μ := by
  have hi := product_integrable μ ν hf hf0 hg hg0 hgi hC
  have hHi : Integrable (Function.uncurry H) (μ.prod ν) :=
    hi.mono' hH.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hdom p.1 p.2)
  refine ⟨hHi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, f x*g x y ∂μ ∂ν := by
      apply integral_mono_ae hHi.integral_prod_right.norm hi.integral_prod_right
      filter_upwards [hi.prod_left_ae] with y hy
      exact norm_integral_le_of_norm_le hy (Filter.Eventually.of_forall fun x => hdom x y)
    _ = ∫ x, ∫ y, f x*g x y ∂ν ∂μ := (integral_integral_swap hi).symm
    _ ≤ _ := product_integral_le μ ν hf hf0 hg hg0 hgi hC

lemma integral_row_bound_ae {F : X → ℝ} (hF : Integrable F μ)
    (H : X → Y → B) (hH : AEStronglyMeasurable (Function.uncurry H) (μ.prod ν))
    (hHi : ∀ᵐ x ∂μ, Integrable (H x) ν)
    (hrow : ∀ᵐ x ∂μ, (∫ y, ‖H x y‖ ∂ν) ≤ F x) :
    Integrable (Function.uncurry H) (μ.prod ν) ∧
    Integrable (fun y => ∫ x, H x y ∂μ) ν ∧
    (∫ y, ‖∫ x, H x y ∂μ‖ ∂ν) ≤ ∫ x, F x ∂μ := by
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    apply (integrable_prod_iff hH).mpr
    refine ⟨hHi, ?_⟩
    apply hF.mono' hH.norm.integral_prod_right'
    filter_upwards [hrow] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hx
  refine ⟨hi, hi.integral_prod_right, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖H x y‖ ∂μ ∂ν := by
      exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = ∫ x, ∫ y, ‖H x y‖ ∂ν ∂μ := (integral_integral_swap hi.norm).symm
    _ ≤ _ := integral_mono_ae hi.norm.integral_prod_left hF hrow

end TamingCompatibility.GeometricHilbert.SchurIntegration

end
end

noncomputable section
namespace TamingCompatibility.GeometricHilbert.SchurKernel
open _root_.MeasureTheory VolterraBounds
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

lemma convolution_row (N : ℕ) {t s A C : ℝ} (ht : 0 < t) (hs : 0 < s)
    (K L : X → X → B) (x : X)
    (hK : Integrable (fun z => weight N t x z * ‖K x z‖) μ)
    (hKI : (∫ z, weight N t x z * ‖K x z‖ ∂μ) ≤ A)
    (hL : StronglyMeasurable (fun zy : X × X => weight N s zy.1 zy.2 * ‖L zy.1 zy.2‖))
    (hLi : ∀ z, Integrable (fun y => weight N s z y * ‖L z y‖) μ)
    (hLI : ∀ z, (∫ y, weight N s z y * ‖L z y‖ ∂μ) ≤ C)
    (hC : 0 ≤ C)
    (hH : StronglyMeasurable (fun zy : X × X =>
      weight N (t+s) x zy.2 • (K x zy.1 * L zy.1 zy.2))) :
    Integrable (fun y => weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖) μ ∧
    (∫ y, weight N (t+s) x y * ‖∫ z, K x z * L z y ∂μ‖ ∂μ) ≤ A*C := by
  have hb : ∀ z y, ‖weight N (t+s) x y • (K x z * L z y)‖ ≤
      (weight N t x z*‖K x z‖)*(weight N s z y*‖L z y‖) := by
    intro z y
    rw [norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
    calc
      _ ≤ weight N (t+s) x y*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (weight_pos N (add_pos ht hs) x y).le
      _ ≤ (weight N t x z*weight N s z y)*(‖K x z‖*‖L z y‖) :=
        mul_le_mul_of_nonneg_right (weight_submultiplicative N ht hs x z y) (by positivity)
      _ = _ := by ring
  have hh := SchurIntegration.norm_integral_row μ μ
    (g := fun z y => weight N s z y*‖L z y‖) hK
    (fun z => mul_nonneg (weight_pos N ht x z).le (norm_nonneg _)) hL
    (fun z y => mul_nonneg (weight_pos N hs z y).le (norm_nonneg _))
    hLi hLI (fun z y => weight N (t+s) x y • (K x z * L z y)) hH hb
  have he (y : X) : ‖∫ z, weight N (t+s) x y • (K x z * L z y) ∂μ‖ =
      weight N (t+s) x y*‖∫ z, K x z * L z y ∂μ‖ := by
    rw [integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N (add_pos ht hs) x y).le]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp_rw [he] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hKI hC])

end TamingCompatibility.GeometricHilbert.SchurKernel

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X]
  [NormedRing B] [NormedAlgebra ℝ B]
variable (μ : Measure X) [SFinite μ]

lemma spatial_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    StronglyMeasurable (fun p : (ℝ × X × X) × ℝ =>
      spatial μ K L p.1.1 p.2 p.1.2.1 p.1.2.2) := by
  have hKm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.1.1-q.1.2, q.1.1.2.1, q.2)) := by fun_prop
  have hLm : Measurable (fun q : ((ℝ × X × X) × ℝ) × X =>
      (q.1.2, q.2, q.1.1.2.2)) := by fun_prop
  exact ((hK.comp_measurable hKm).mul (hL.comp_measurable hLm)).integral_prod_right

lemma convolution_measurable (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) :
    MeasurableKernel (convolution μ K L) := by
  have hm := spatial_measurable μ K L hK hL
  have hset : MeasurableSet {p : (ℝ × X × X) × ℝ | p.2 ∈ Ioo 0 p.1.1} := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.fst))
  have hmi : StronglyMeasurable (Function.uncurry (fun (p : ℝ × X × X) (s : ℝ) =>
      (Ioo 0 p.1).indicator (fun s => spatial μ K L p.1 s p.2.1 p.2.2) s)) :=
    hm.indicator hset
  have hi := hmi.integral_prod_right (ν := volume)
  simpa only [MeasurableKernel, convolution, integral_indicator measurableSet_Ioo] using hi

lemma spatial_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t x y) :
    StronglyMeasurable (fun s => spatial μ K L t s x y) :=
  (spatial_measurable μ K L hK hL).comp_measurable
    (show Measurable (fun s : ℝ => ((t,x,y),s)) from
      measurable_const.prodMk measurable_id)

omit [NormedAlgebra ℝ B] in
lemma product_section (K L : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (hL : MeasurableKernel L) (t s x y) :
    StronglyMeasurable (fun z => K (t-s) x z * L s z y) := by
  exact (hK.comp_measurable (measurable_const.prodMk
    (measurable_const.prodMk measurable_id))).mul
    (hL.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

variable [PseudoMetricSpace X] [BorelSpace X] [SecondCountableTopology X]

omit [BorelSpace X] [SecondCountableTopology X] in
lemma convolution_sup (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    IntegrableOn (fun s => spatial μ K L t s x y) (Ioo 0 t) ∧
    weight N t x y*‖convolution μ K L t x y‖ ≤ 4*A*C/t := by
  have ha (s : ℝ) (hs : s ∈ Ioo 0 t) : t-s ∈ Ioc 0 T :=
    ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb (s : ℝ) (hs : s ∈ Ioo 0 t) : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  exact time_convolution_bound μ N ht.1 hK.nonneg hL.nonneg K L x y
    (fun s hs z => hK.sup _ (ha s hs) x z)
    (fun s hs z => hL.sup _ (hb s hs) z y)
    (fun s hs => hK.row_int _ (ha s hs) x)
    (fun s hs => hL.col_int _ (hb s hs) y)
    (fun s hs => hK.row _ (ha s hs) x)
    (fun s hs => hL.col _ (hb s hs) y)
    (fun s _ => (product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable)
    (spatial_section μ K L hK.measurable hL.measurable t x y).aestronglyMeasurable

omit [NormedAlgebra ℝ B] in
lemma weighted_section (N : ℕ) (K : Kernel (X := X) (B := B))
    (hK : MeasurableKernel K) (t : ℝ) :
    StronglyMeasurable (fun p : X × X => weight N t p.1 p.2*‖K t p.1 p.2‖) := by
  have hw : Continuous (fun p : X × X => weight N t p.1 p.2) := by
    unfold weight
    fun_prop
  exact hw.stronglyMeasurable.mul (kernel_section K hK t).norm

lemma spatial_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (x : X) :
    Integrable (fun y => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ y, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  have hweight : StronglyMeasurable (fun zy : X × X => weight N ((t-s)+s) x zy.2) :=
    ((weight_continuous N ((t-s)+s) x).comp continuous_snd).stronglyMeasurable
  have hKm : StronglyMeasurable (fun zy : X × X => K (t-s) x zy.1) :=
    hK.measurable.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  have hr := SchurKernel.convolution_row μ N ha.1 hb.1 (K (t-s)) (L s) x
    (hK.row_int _ ha x) (hK.row _ ha x) (weighted_section N L hL.measurable s)
    (hL.row_int _ hb) (hL.row _ hb) hL.nonneg
    (hweight.smul (hKm.mul (kernel_section L hL.measurable s)))
  simpa [spatial] using hr

lemma convolution_row (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : X) :
    Integrable (fun y => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ y, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s y => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (y : X) : ‖H s y‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hweight : StronglyMeasurable (fun p : ℝ × X => weight N t x p.2) :=
      ((weight_continuous N t x).comp continuous_snd).stronglyMeasurable
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,x,p.2),p.1)) from by fun_prop)
    exact hweight.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun y => ‖H s y‖) μ
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ y, ‖H s y‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_row μ N K L hK hL ht hs x).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (y : X) : ‖∫ s in Ioo 0 t, H s y‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma spatial_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t) (y : X) :
    Integrable (fun x => weight N t x y*‖spatial μ K L t s x y‖) μ ∧
    (∫ x, weight N t x y*‖spatial μ K L t s x y‖ ∂μ) ≤ A*C := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2, (sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1, hs.2.le.trans ht.2⟩
  let f : X → ℝ := fun z => weight N s z y*‖L s z y‖
  let g : X → X → ℝ := fun z x => weight N (t-s) x z*‖K (t-s) x z‖
  let H : X → X → B := fun z x => weight N t x y • (K (t-s) x z * L s z y)
  have hdom (z x : X) : ‖H z x‖ ≤ f z*g z x := by
    rw [show ‖H z x‖ = weight N t x y*‖K (t-s) x z * L s z y‖ by
      simp [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]]
    have hw : weight N t x y ≤ weight N (t-s) x z*weight N s z y := by
      simpa using weight_submultiplicative N ha.1 hb.1 x z y
    calc
      _ ≤ (weight N (t-s) x z*weight N s z y)*(‖K (t-s) x z‖*‖L s z y‖) :=
        mul_le_mul hw (norm_mul_le _ _) (norm_nonneg _)
          (mul_nonneg (weight_pos N ha.1 x z).le (weight_pos N hb.1 z y).le)
      _ = _ := by dsimp [f,g] <;> ring
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (weighted_section N K hK.measurable (t-s)).comp_measurable measurable_swap
  have hH : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : X × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hk := (kernel_section K hK.measurable (t-s)).comp_measurable measurable_swap
    have hl : StronglyMeasurable (fun p : X × X => L s p.1 y) :=
      hL.measurable.comp_measurable (measurable_const.prodMk (measurable_fst.prodMk measurable_const))
    exact hw.stronglyMeasurable.smul (hk.mul hl)
  have hh := SchurIntegration.norm_integral_row μ μ (g := g) (hL.col_int _ hb y)
    (fun z => mul_nonneg (weight_pos N hb.1 z y).le (norm_nonneg _)) hg
    (fun z x => mul_nonneg (weight_pos N ha.1 x z).le (norm_nonneg _))
    (hK.col_int _ ha) (hK.col _ ha) H hH hdom
  have he (x : X) : ‖∫ z, H z x ∂μ‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le, spatial]
  refine ⟨?_, ?_⟩
  · simpa only [he] using hh.1.norm
  · have h := hh.2
    simp only [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hL.col _ hb y) hK.nonneg)

lemma convolution_col (N : ℕ) {T A C : ℝ} (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => weight N t x y*‖convolution μ K L t x y‖) μ ∧
    (∫ x, weight N t x y*‖convolution μ K L t x y‖ ∂μ) ≤ t*A*C := by
  let H : ℝ → X → B := fun s x => weight N t x y • spatial μ K L t s x y
  have he (s : ℝ) (x : X) : ‖H s x‖ = weight N t x y*‖spatial μ K L t s x y‖ := by
    simp only [H, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le]
  have hm : StronglyMeasurable (Function.uncurry H) := by
    have hw : Continuous (fun p : ℝ × X => weight N t p.2 y) := by unfold weight; fun_prop
    have hsp := (spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,p.2,y),p.1)) from by fun_prop)
    exact hw.stronglyMeasurable.smul hsp
  have hi : ∀ᵐ s ∂volume.restrict (Ioo 0 t), Integrable (H s) μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    apply (integrable_norm_iff (hm.comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mp
    change Integrable (fun x => ‖H s x‖) μ
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).1
  have hr : ∀ᵐ s ∂volume.restrict (Ioo 0 t), (∫ x, ‖H s x‖ ∂μ) ≤ A*C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [he] using (spatial_col μ N K L hK hL ht hs y).2
  have hh := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrableOn_const (C := A*C) (hs := measure_Ioo_lt_top.ne)) H hm.aestronglyMeasurable hi hr
  have hei (x : X) : ‖∫ s in Ioo 0 t, H s x‖ = weight N t x y*‖convolution μ K L t x y‖ := by
    simp only [H, integral_smul, norm_smul, Real.norm_of_nonneg (weight_pos N ht.1 x y).le,
      convolution]
  refine ⟨?_, ?_⟩
  · simpa only [hei] using hh.2.1.norm
  · have hb := hh.2.2
    simp only [hei, integral_const, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le ht.1.le, sub_zero, smul_eq_mul] at hb
    simpa only [mul_assoc] using hb

lemma convolution_heatBound (N : ℕ) {T A C : ℝ} (hT : 0 ≤ T)
    (K L : Kernel (X := X) (B := B))
    (hK : HeatBound μ N T A K) (hL : HeatBound μ N T C L) :
    HeatBound μ N T (4*T*A*C) (convolution μ K L) := by
  refine ⟨convolution_measurable μ K L hK.measurable hL.measurable,
    by have hA := hK.nonneg; have hC := hL.nonneg; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x y
    apply (convolution_sup μ N K L hK hL ht x y).2.trans
    apply (div_le_div_iff₀ ht.1 (sq_pos_of_pos ht.1)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2)
      (mul_nonneg (mul_nonneg hK.nonneg hL.nonneg) ht.1.le)]
  · intro t ht x
    exact (convolution_row μ N K L hK hL ht x).1
  · intro t ht x
    apply (convolution_row μ N K L hK hL ht x).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg
  · intro t ht y
    exact (convolution_col μ N K L hK hL ht y).1
  · intro t ht y
    apply (convolution_col μ N K L hK hL ht y).2.trans
    have ht' : t ≤ 4*T := by linarith [ht.2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht' hK.nonneg) hL.nonneg

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalKernelForms
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma framePairing_continuous (a : TwoForm X) (ha : IsSmooth a) :
    Continuous (framePairing A J α ht E a) := by
  unfold framePairing
  apply (squareMass_inv_smooth A).continuous.smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact (GeometricAdjoint.pairing_two_smooth J α hs ht ha
    (globalFrame_smooth J α ht A E hE hs p j)).continuous.smul continuous_const

include hs hE in
lemma framePairing_bound (a : TwoForm X) (ha : IsSmooth a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖framePairing A J α ht E a x‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (framePairing_continuous A J α hs ht E hE a ha).continuousOn
  exact ⟨max C 0,le_max_right _ _,fun x => (hC x (mem_univ x)).trans (le_max_left _ _)⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelTestTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
omit [ConnectedSpace X] [SecondCountableTopology X] in
lemma kernelTestLinear_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a) :
    StronglyMeasurable (Function.uncurry (kernelTestLinear A J α ht E K a)) := by
  let := geometricVolume_finite A J α hs ht
  have hφ := (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X =>
      (framePairing A J α ht E a p.2).comp (K p.1.1 p.2 p.1.2)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
      ((hφ.comp_measurable measurable_snd).prodMk
        (hK.comp_measurable (show Measurable (fun p : (ℝ × X) × X =>
          (p.1.1,p.2,p.1.2)) by fun_prop)))
  exact hm.integral_prod_right

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) :
    Integrable (fun x => (framePairing A J α ht E a x).comp (K t x y))
      (geometricVolume A J α) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,_hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hi := hK.col_int t htp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi
  have hm : StronglyMeasurable (fun x => (framePairing A J α ht E a x).comp (K t x y)) :=
    (continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
    ((framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable.prodMk
      (hK.measurable.comp_measurable (measurable_const.prodMk (measurable_id.prodMk measurable_const))))
  apply (hi.const_mul B).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_apply
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T) (y : X) (v : FrameSpace A) :
    kernelTestLinear A J α ht E K a t y v = kernelTestSlice A J α ht E K y v a t :=
  ContinuousLinearMap.integral_apply (kernelTestLinear_integrable A J α hs ht E hE K hK a ha htp y) v

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelTestLinear_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  refine ⟨B*H,mul_nonneg hB hK.nonneg,?_⟩
  intro t hp y
  have hi := hK.col_int t hp y
  have hb := hK.col t hp y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
  calc
    _ ≤ ∫ x, B*‖K t x y‖ ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (hi.const_mul B)
      exact Eventually.of_forall fun x => (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg _))
    _ = B*(∫ x, ‖K t x y‖ ∂geometricVolume A J α) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hB

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open Set Filter _root_.MeasureTheory
open scoped Topology
variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] [CompleteSpace F] in
lemma action_integrable (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hvm : StronglyMeasurable v)
    {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) (x : X)
    (hKi : Integrable (fun y => ‖K x y‖) μ) : Integrable (fun y => K x y (v y)) μ := by
  apply (hKi.mul_const V).mono'
    (((applied_measurable K hK v hvm).comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with y
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))

lemma action_test_swap (K : X → X → F →L[ℝ] F)
    (hK : StronglyMeasurable (Function.uncurry K)) (v : X → F) (hvm : StronglyMeasurable v)
    (φ : X → F →L[ℝ] ℝ) (hφm : StronglyMeasurable φ)
    {M V C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hKb : ∀ x y, ‖K x y‖ ≤ M) (hv : ∀ y, ‖v y‖ ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, φ x (action μ K v x) ∂μ) = ∫ y, ∫ x, φ x (K x y (v y)) ∂μ ∂μ := by
  have hbound (x y : X) : ‖K x y (v y)‖ ≤ M*V :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hKb x y) (hv y) (norm_nonneg _) hM)
  have hm := applied_measurable K hK v hvm
  have htm : StronglyMeasurable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hφm.comp_measurable measurable_fst).prodMk hm)
  have hi (x : X) : Integrable (fun y => K x y (v y)) μ := by
    apply (integrable_const (M*V)).mono'
      ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    exact Eventually.of_forall (hbound x)
  have ht : Integrable (fun p : X × X => φ p.1 (K p.1 p.2 (v p.2))) (μ.prod μ) := by
    apply (integrable_const (C*(M*V))).mono' htm.aestronglyMeasurable
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ _) (hbound _ _) (norm_nonneg _) hC)
  calc
    _ = ∫ x, ∫ y, φ x (K x y (v y)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((φ x).integral_comp_comm (hi x)).symm
    _ = _ := integral_integral_swap ht

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)
lemma HeatBound.mono_time {N : ℕ} {S T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) (hST : S ≤ T) : HeatBound μ N S A K := by
  have hsub : Ioc 0 S ⊆ Ioc 0 T := Ioc_subset_Ioc_right hST
  exact ⟨h.measurable,h.nonneg,fun t ht => h.sup t (hsub ht),
    fun t ht => h.row_int t (hsub ht),fun t ht => h.row t (hsub ht),
    fun t ht => h.col_int t (hsub ht),fun t ht => h.col t (hsub ht)⟩
end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open _root_.MeasureTheory Set Filter
variable {X F : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : ℝ → X → X → F →L[ℝ] F) {T A C : ℝ}
  (hK : VolterraKernel.HeatBound μ 0 T A K) (hL : VolterraKernel.HeatBound μ 0 T C L)

include hK hL in
omit [BorelSpace X] in
lemma spatial_action {t s : ℝ} (ht : t ∈ Ioc 0 T) (hs : s ∈ Ioo 0 t)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (_hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) :
    action μ (VolterraKernel.spatial μ K L t s) v x =
      action μ (K (t-s)) (action μ (L s) v) x := by
  have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
  have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
  have hKi := hK.row_int (t-s) ha x
  have hLi (z : X) := hL.row_int s hb z
  have hLb (z : X) := hL.row s hb z
  have hLs (z y : X) := hL.sup s hb z y
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hKi hLi hLb hLs
  have hKm : StronglyMeasurable (fun z => K (t-s) x z) :=
    hK.measurable.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hLm := VolterraKernel.kernel_section L hL.measurable s
  have hn := SchurIntegration.product_integrable μ μ (g := fun z y => ‖L s z y‖) hKi (fun _ => norm_nonneg _)
    hLm.norm (fun _ _ => norm_nonneg _) hLi hLb
  have hpm : StronglyMeasurable (fun p : X × X => K (t-s) x p.1 (L s p.1 p.2 (v p.2))) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hKm.comp_measurable measurable_fst).prodMk (applied_measurable (L s) hLm v hvm))
  have hpi : Integrable (fun p : X × X => K (t-s) x p.1 (L s p.1 p.2 (v p.2))) (μ.prod μ) := by
    apply (hn.mul_const V).mono' hpm.aestronglyMeasurable
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _))) (norm_nonneg _)).trans_eq (by ring))
  have hz (y : X) : Integrable (fun z => K (t-s) x z * L s z y) μ := by
    apply (hKi.mul_const (C/s^2)).mono'
      (VolterraKernel.product_section K L hK.measurable hL.measurable t s x y).aestronglyMeasurable
    filter_upwards [] with z
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hLs z y) (norm_nonneg _))
  calc
    _ = ∫ y, ∫ z, K (t-s) x z (L s z y (v y)) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact ContinuousLinearMap.integral_apply (hz y) (v y)
    _ = ∫ z, ∫ y, K (t-s) x z (L s z y (v y)) ∂μ ∂μ := (integral_integral_swap hpi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (K (t-s) x z).integral_comp_comm (action_integrable μ (L s) hLm v hvm hv z (hLi z))

include hK hL in
lemma convolution_action {t : ℝ} (ht : t ∈ Ioc 0 T)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (x : X) :
    action μ (VolterraKernel.convolution μ K L t) v x =
      ∫ s in Ioo 0 t, action μ (K (t-s)) (action μ (L s) v) x := by
  have hsm : StronglyMeasurable (fun p : ℝ × X => VolterraKernel.spatial μ K L t p.1 x p.2) :=
    (VolterraKernel.spatial_measurable μ K L hK.measurable hL.measurable).comp_measurable
      (show Measurable (fun p : ℝ × X => ((t,x,p.2),p.1)) by fun_prop)
  have hm : StronglyMeasurable (fun p : ℝ × X => VolterraKernel.spatial μ K L t p.1 x p.2 (v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hsm.prodMk (hvm.comp_measurable measurable_snd))
  have hrow (s : ℝ) (hs : s ∈ Ioo 0 t) := VolterraKernel.spatial_row μ 0 K L hK hL ht hs x
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hrow
  have hi := SchurIntegration.integral_row_bound_ae (volume.restrict (Ioo 0 t)) μ
    (integrable_const (A*C*V)) (fun s y => VolterraKernel.spatial μ K L t s x y (v y))
    hm.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      apply ((hrow s hs).1.mul_const V).mono'
        ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      calc
        _ ≤ ∫ y, ‖VolterraKernel.spatial μ K L t s x y‖*V ∂μ := by
          apply integral_mono_ae
            (((hrow s hs).1.mul_const V).mono'
              ((hm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
              (Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _)))).norm
            ((hrow s hs).1.mul_const V)
          exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (hv y) (norm_nonneg _))
        _ = (∫ y, ‖VolterraKernel.spatial μ K L t s x y‖ ∂μ)*V := integral_mul_const _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hrow s hs).2 hV)
  calc
    _ = ∫ y, (∫ s in Ioo 0 t, VolterraKernel.spatial μ K L t s x y (v y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact ContinuousLinearMap.integral_apply (VolterraKernel.convolution_sup μ 0 K L hK hL ht x y).1 (v y)
    _ = ∫ s in Ioo 0 t, ∫ y, VolterraKernel.spatial μ K L t s x y (v y) ∂μ :=
      (integral_integral_swap hi.1).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      exact spatial_action μ K L hK hL ht hs v hvm hV hv x

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraPairing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.KernelL2
open _root_.MeasureTheory Set Filter
variable {X F : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (K L : ℝ → X → X → F →L[ℝ] F) {T A C : ℝ}
  (hK : VolterraKernel.HeatBound μ 0 T A K) (hL : VolterraKernel.HeatBound μ 0 T C L)

omit [BorelSpace X] [CompleteSpace F] in
lemma time_action_measurable (hKm : VolterraKernel.MeasurableKernel K)
    (v : X → F) (hvm : StronglyMeasurable v) :
    StronglyMeasurable (fun p : ℝ × X => action μ (K p.1) v p.2) := by
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X => K p.1.1 p.1.2 p.2 (v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hKm.comp_measurable (show Measurable (fun p : (ℝ × X) × X => (p.1.1,p.1.2,p.2)) by fun_prop)).prodMk (hvm.comp_measurable measurable_snd))
  exact hm.integral_prod_right

include hK hL in
omit [BorelSpace X] [CompleteSpace F] in
lemma shifted_action_measurable (t : ℝ) (v : X → F) (hvm : StronglyMeasurable v) :
    StronglyMeasurable (fun p : ℝ × X => action μ (K (t-p.1)) (action μ (L p.1) v) p.2) := by
  have hLm := time_action_measurable μ L hL.measurable v hvm
  have hm : StronglyMeasurable (fun p : (ℝ × X) × X => K (t-p.1.1) p.1.2 p.2
      (action μ (L p.1.1) v p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hK.measurable.comp_measurable (show Measurable (fun p : (ℝ × X) × X => (t-p.1.1,p.1.2,p.2)) by fun_prop)).prodMk
        (hLm.comp_measurable (measurable_fst.fst.prodMk measurable_snd)))
  exact hm.integral_prod_right

include hK hL in
lemma convolution_pairing {t : ℝ} (ht : t ∈ Ioc 0 T)
    (v : X → F) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (φ : X → F →L[ℝ] ℝ) (hφm : StronglyMeasurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ x, ‖φ x‖ ≤ B) :
    (∫ x, φ x (action μ (VolterraKernel.convolution μ K L t) v x) ∂μ) =
      ∫ s in Ioo 0 t, ∫ x, φ x (action μ (K (t-s)) (action μ (L s) v) x) ∂μ := by
  have hm := shifted_action_measurable μ K L hK hL t v hvm
  have hn (s : ℝ) (hs : s ∈ Ioo 0 t) (x : X) :
      ‖action μ (K (t-s)) (action μ (L s) v) x‖ ≤ A*(C*V) := by
    have ha : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hs.2,(sub_le_self _ hs.1.le).trans ht.2⟩
    have hb : s ∈ Ioc 0 T := ⟨hs.1,hs.2.le.trans ht.2⟩
    have hKi := hK.row_int (t-s) ha x
    have hKb := hK.row (t-s) ha x
    have hLi (z : X) := hL.row_int s hb z
    have hLb (z : X) := hL.row s hb z
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hKi hKb hLi hLb
    exact action_norm μ (K (t-s)) (action μ (L s) v) (mul_nonneg hL.nonneg hV)
      (fun z => action_norm μ (L s) v hV hv z (hLi z) (hLb z)) x hKi hKb
  have htm : StronglyMeasurable (fun p : ℝ × X =>
      φ p.2 (action μ (K (t-p.1)) (action μ (L p.1) v) p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hφm.comp_measurable measurable_snd).prodMk hm)
  have hi : Integrable (fun p : ℝ × X =>
      φ p.2 (action μ (K (t-p.1)) (action μ (L p.1) v) p.2))
      ((volume.restrict (Ioo 0 t)).prod μ) := by
    apply Integrable.of_bound htm.aestronglyMeasurable (B*(A*(C*V)))
    have hp : ∀ᵐ p : ℝ × X ∂(volume.restrict (Ioo 0 t)).prod μ, p.1 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact Eventually.of_forall fun _ => hs
    filter_upwards [hp] with p hp
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ p.2) (hn p.1 hp p.2) (norm_nonneg _) hB)
  calc
    _ = ∫ x, φ x (∫ s in Ioo 0 t, action μ (K (t-s)) (action μ (L s) v) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [convolution_action μ K L hK hL ht v hvm hV hv x]
    _ = ∫ x, (∫ s in Ioo 0 t, φ x (action μ (K (t-s)) (action μ (L s) v) x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply ((φ x).integral_comp_comm _).symm
      apply Integrable.of_bound
        ((hm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (A*(C*V))
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hn s hs x
    _ = _ := (integral_integral_swap hi).symm

end TamingCompatibility.GeometricHilbert.KernelL2

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_eq_weakAction
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) :
    kernelInputTest A J α ht E K a t v = kernelWeakAction A J α ht E K v a t := by
  apply integral_congr_ae
  filter_upwards [] with y
  exact kernelTestLinear_apply A J α hs ht E hE K hK a ha htp y (v y)

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_action
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E K a t v =
      ∫ x, framePairing A J α ht E a x (KernelL2.action (geometricVolume A J α) (K t) v x)
        ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hsup := hK.sup t htp
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hsup
  rw [kernelInputTest_eq_weakAction A J α hs ht E hE K hK a ha htp v]
  exact (KernelL2.action_test_swap (geometricVolume A J α) (K t)
    (VolterraKernel.kernel_section K hK.measurable t) v hvm (framePairing A J α ht E a)
    (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable
    (div_nonneg hK.nonneg (sq_nonneg t)) hB hsup hv hφ).symm

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_shift_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (W : ℝ → X → FrameSpace A) (hW : StronglyMeasurable (Function.uncurry W)) :
    StronglyMeasurable (fun p : ℝ × ℝ => kernelInputTest A J α ht E K a (p.1-p.2) (W p.2)) := by
  let := geometricVolume_finite A J α hs ht
  have hkm := kernelTestLinear_measurable A J α hs ht E hE K hK a ha
  have hm : StronglyMeasurable (fun p : (ℝ × ℝ) × X =>
      kernelTestLinear A J α ht E K a (p.1.1-p.1.2) p.2 (W p.1.2 p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((hkm.comp_measurable (show Measurable (fun p : (ℝ × ℝ) × X => (p.1.1-p.1.2,p.2)) by fun_prop)).prodMk
        (hW.comp_measurable (measurable_fst.snd.prodMk measurable_snd)))
  exact hm.integral_prod_right

include hs in
omit [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A) (a : TwoForm X)
    (t : ℝ) (v : X → FrameSpace A) {B V : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ y, ‖kernelTestLinear A J α ht E K a t y‖ ≤ B) (hv : ∀ y, ‖v y‖ ≤ V) :
    ‖kernelInputTest A J α ht E K a t v‖ ≤ (geometricVolume A J α).real univ*(B*V) := by
  let := geometricVolume_finite A J α hs ht
  calc
    _ ≤ ∫ y : X, B*V ∂geometricVolume A J α := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hφ y) (hv y) (norm_nonneg _) hB)
    _ = _ := by simp [integral_const,smul_eq_mul]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeBoundedInputPrimitive
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma bounded_input_leading_primitive (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    {V : ℝ} (_hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in Ioo 0 t, ∫ y,
      (kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val s y -
       kernelTestLinear A J α ht E (globalLeading J α ht A E)
         (hodgeLaplacian A J α hs ht a).val s y) (v y) ∂geometricVolume A J α) =
      ∫ y, kernelTestLinear A J α ht E (globalLeading J α ht A E) a.val t y (v y) -
        framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hRb⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE _ hR a.val a.property
  obtain ⟨C,hC,hLb⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
  let G := fun p : ℝ × X =>
    (kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val p.1 p.2 -
     kernelTestLinear A J α ht E (globalLeading J α ht A E)
       (hodgeLaplacian A J α hs ht a).val p.1 p.2) (v p.2)
  have hm : StronglyMeasurable G := by
    exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (((kernelTestLinear_measurable A J α hs ht E hE _ hR.measurable a.val a.property).sub
      (kernelTestLinear_measurable A J α hs ht E hE _ hL.measurable
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property)).prodMk
      (hvm.comp_measurable measurable_snd))
  have hi : Integrable G ((volume.restrict (Ioo 0 t)).prod (geometricVolume A J α)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable ((B+C)*V)
    have hp : ∀ᵐ p : ℝ × X ∂(volume.restrict (Ioo 0 t)).prod (geometricVolume A J α),
        p.1 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs'
      exact Eventually.of_forall fun _ => hs'
    filter_upwards [hp] with p hp
    have hpt : p.1 ∈ Ioc 0 1 := ⟨hp.1,hp.2.le.trans ht1⟩
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hRb _ hpt _) (hLb _ hpt _)))
        (hv _) (norm_nonneg _) (add_nonneg hB hC))
  calc
    _ = ∫ y, (∫ s in Ioo 0 t, G (s,y)) ∂geometricVolume A J α := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [kernelTestLinear_apply A J α hs ht E hE _ hL a.val a.property ⟨htp,ht1⟩ y (v y)]
      rw [← leading_time_primitive A J α hs ht E hE y (v y) a htp ht1,
        intervalIntegral.integral_of_le htp.le, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hp
      have hsp : s ∈ Ioc 0 1 := ⟨hp.1,hp.2.le.trans ht1⟩
      change kernelTestLinear A J α ht E (globalResidual J α ht A E) a.val s y (v y) -
        kernelTestLinear A J α ht E (globalLeading J α ht A E)
          (hodgeLaplacian A J α hs ht a).val s y (v y) = _
      rw [kernelTestLinear_apply A J α hs ht E hE _ hR a.val a.property hsp y (v y),
        kernelTestLinear_apply A J α hs ht E hE _ hL
          (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hsp y (v y)]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [SecondCountableTopology X] in
lemma kernelTestLinear_input_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    Integrable (fun y => kernelTestLinear A J α ht E K a t y (v y)) (geometricVolume A J α) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE K hK a ha
  have hkm : StronglyMeasurable (fun y => kernelTestLinear A J α ht E K a t y) := (kernelTestLinear_measurable A J α hs ht E hE K hK.measurable a ha).comp_measurable
    (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    (hkm.prodMk hm)).aestronglyMeasurable (B*V)
  exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hφ t htp y) (hv y) (norm_nonneg _) hB)

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma kernelInputTest_uniform_bound
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {V : ℝ} (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc 0 T, ∀ v : X → FrameSpace A,
      (∀ y, ‖v y‖ ≤ V) → ‖kernelInputTest A J α ht E K a t v‖ ≤ B := by
  obtain ⟨B,hB,hφ⟩ := kernelTestLinear_uniform_bound A J α hs ht E hE K hK a ha
  refine ⟨(geometricVolume A J α).real univ*(B*V),by positivity,?_⟩
  intro t hp v hv
  exact kernelInputTest_bound A J α hs ht E K a t v hB (hφ t hp) hv

include hs hE in
omit [ConnectedSpace X] in
lemma kernelInputTest_time_measurable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : VolterraKernel.MeasurableKernel K) (a : TwoForm X) (ha : IsSmooth a)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) :
    StronglyMeasurable (fun t => kernelInputTest A J α ht E K a t v) := by
  have hh := kernelInputTest_shift_measurable A J α hs ht E hE K hK a ha
    (fun _ => v) (hm.comp_measurable measurable_snd)
  simpa [Function.comp_def] using hh.comp_measurable (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian
include hE in
lemma kernelInputTest_leading_primitive
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v)
    {V : ℝ} (hV : 0 ≤ V) (hv : ∀ y, ‖v y‖ ≤ V)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) (ht1 : t ≤ 1) :
    (∫ s in Ioo 0 t,
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v -
      kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val s v) =
      kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v -
        ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  have hiφ : Integrable (fun y => framePairing A J α ht E a.val y (v y)) (geometricVolume A J α) := by
    apply Integrable.of_bound ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      ((framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable.prodMk hvm)).aestronglyMeasurable (B*V)
    exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hφ y) (hv y) (norm_nonneg _) hB)
  have hp := bounded_input_leading_primitive A J α hs ht E hE v hvm hV hv a htp ht1
  rw [integral_sub (kernelTestLinear_input_integrable A J α hs ht E hE _ hL a.val a.property
    ⟨htp,ht1⟩ v hvm hv) hiφ] at hp
  refine Eq.trans ?_ hp
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hsp
  have hst : s ∈ Ioc 0 1 := ⟨hsp.1,hsp.2.le.trans ht1⟩
  exact (integral_sub
    (kernelTestLinear_input_integrable A J α hs ht E hE _ hR a.val a.property hst v hvm hv)
    (kernelTestLinear_input_integrable A J α hs ht E hE _ hL
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hst v hvm hv)).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCandidateL2Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter _root_.MeasureTheory
open scoped Topology

lemma of_primitive {I : Type*} (D : I → I) (F : I → ℝ → ℝ) (f : I → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hi : ∀ a, IntegrableOn (F a) (Icc 0 T))
    (hp : ∀ a, ∀ t ∈ Icc 0 T, F a t = f a - ∫ s in Ioo 0 t, F (D a) s) :
    (∀ a, ContinuousOn (F a) (Icc 0 T)) ∧
      (∀ a, ∀ t ∈ Ioo 0 T, HasDerivAt (F a) (-F (D a) t) t) := by
  have he (a : I) (t : ℝ) (ht : t ∈ Icc 0 T) :
      F a t = f a - ∫ s in 0..t, F (D a) s := by
    rw [hp a t ht,intervalIntegral.integral_of_le ht.1,integral_Ioc_eq_integral_Ioo]
  have hc (a : I) : ContinuousOn (F a) (Icc 0 T) := by
    have hh : ContinuousOn (fun t => ∫ s in 0..t, F (D a) s) (Icc 0 T) := by
      have hh := intervalIntegral.continuousOn_primitive_interval (show IntegrableOn (F (D a)) (uIcc 0 T) by
        simpa [uIcc_of_le hT] using hi (D a))
      simpa [uIcc_of_le hT] using hh
    exact (continuousOn_const.sub hh).congr (fun t ht => he a t ht)
  refine ⟨hc,?_⟩
  intro a t ht
  have hcc : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hcont : ContinuousAt (F (D a)) t := (hc (D a) t ⟨ht.1.le,ht.2.le⟩).continuousAt hcc
  have hint : IntervalIntegrable (F (D a)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mpr
      ((hi (D a)).mono_set (Icc_subset_Icc_right ht.2.le))
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    ⟨Icc 0 T,hcc,(hi (D a)).aestronglyMeasurable⟩ hcont).const_sub (f a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hcc] with s hs
  exact he a s hs

end TamingCompatibility.GeometricHilbert.WeakHeat

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputDuhamel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma kernelInputTest_convolution
    (K L : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C L)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E (VolterraKernel.convolution (geometricVolume A J α) K L) a t v =
      ∫ s in Ioo 0 t, kernelInputTest A J α ht E K a (t-s)
        (KernelL2.action (geometricVolume A J α) (L s) v) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a ha
  have hconv := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0
    (htp.1.le.trans htp.2) K L hK hL
  rw [kernelInputTest_action A J α hs ht E hE _ hconv a ha htp v hvm hv]
  rw [KernelL2.convolution_pairing (geometricVolume A J α) K L hK hL htp v hvm hV hv
    (framePairing A J α ht E a) (framePairing_continuous A J α hs ht E hE a ha).stronglyMeasurable hB hφ]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hsp
  have ha' : t-s ∈ Ioc 0 T := ⟨sub_pos.mpr hsp.2,(sub_le_self _ hsp.1.le).trans htp.2⟩
  have hb' : s ∈ Ioc 0 T := ⟨hsp.1,hsp.2.le.trans htp.2⟩
  have hr (x : X) := hL.row_int s hb' x
  have hb (x : X) := hL.row s hb' x
  simp only [VolterraBounds.weight,pow_zero,one_mul] at hr hb
  exact (kernelInputTest_action A J α hs ht E hE K hK a ha ha'
    (KernelL2.action (geometricVolume A J α) (L s) v)
    (KernelL2.action_measurable (geometricVolume A J α) (L s)
      (VolterraKernel.kernel_section L hL.measurable s) v hvm)
    (fun x => KernelL2.action_norm (geometricVolume A J α) (L s) v hV hv x (hr x) (hb x))).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open _root_.MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integral_swap {t : ℝ} (G : ℝ → ℝ → E)
    (hG : StronglyMeasurable (Function.uncurry G)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s ∈ Ioo 0 t, ∀ u ∈ Ioo s t, ‖G u s‖ ≤ B) :
    (∫ s in Ioo 0 t, ∫ u in Ioo s t, G u s) =
      ∫ u in Ioo 0 t, ∫ s in Ioo 0 u, G u s := by
  let F := fun p : ℝ × ℝ => if p.1 < p.2 then G p.2 p.1 else 0
  have hFm : StronglyMeasurable F :=
    (hG.comp_measurable measurable_swap).piecewise
      (measurableSet_lt measurable_fst measurable_snd) stronglyMeasurable_const
  have hFi : Integrable F ((volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t))) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable B
    have hp : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioo 0 t)).prod (volume.restrict (Ioo 0 t)),
        p.1 ∈ Ioo 0 t ∧ p.2 ∈ Ioo 0 t := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact ⟨hs,hu⟩
    filter_upwards [hp] with p hp
    dsimp [F]
    split_ifs with h
    · exact hb p.1 hp.1 p.2 ⟨h,hp.2.2⟩
    · simpa using hB
  have hleft (s : ℝ) (hs : s ∈ Ioo 0 t) :
      (∫ u in Ioo 0 t, F (s,u)) = ∫ u in Ioo s t, G u s := by
    have heq : (Ioi s) ∩ Ioo 0 t = Ioo s t := by ext u; simp only [mem_inter_iff,mem_Ioi,mem_Ioo]; constructor <;> intro h <;> grind
    change (∫ u in Ioo 0 t, (Ioi s).indicator (fun u => G u s) u) = _
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,heq]
  have hright (u : ℝ) (hu : u ∈ Ioo 0 t) :
      (∫ s in Ioo 0 t, F (s,u)) = ∫ s in Ioo 0 u, G u s := by
    have heq : (Iio u) ∩ Ioo 0 t = Ioo 0 u := by ext s; simp only [mem_inter_iff,mem_Iio,mem_Ioo]; constructor <;> intro h <;> grind
    change (∫ s in Ioo 0 t, (Iio u).indicator (fun s => G u s) s) = _
    rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,heq]
  calc
    _ = ∫ s in Ioo 0 t, ∫ u in Ioo 0 t, F (s,u) := by
      apply setIntegral_congr_fun measurableSet_Ioo; intro s hs; exact (hleft s hs).symm
    _ = ∫ u in Ioo 0 t, ∫ s in Ioo 0 t, F (s,u) := integral_integral_swap hFi
    _ = _ := setIntegral_congr_fun measurableSet_Ioo hright

end TamingCompatibility.GeometricHilbert.TimeTriangle

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open _root_.MeasureTheory Set Filter

lemma integrated_primitive {t : ℝ} (F A : ℝ → ℝ) (G : ℝ → ℝ → ℝ)
    (hF : IntegrableOn F (Ioo 0 t)) (hA : IntegrableOn A (Ioo 0 t))
    (hG : StronglyMeasurable (Function.uncurry G)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ s ∈ Ioo 0 t, ∀ u ∈ Ioo s t, ‖G u s‖ ≤ B)
    (hp : ∀ s ∈ Ioo 0 t, F s-A s = ∫ u in Ioo s t, G u s) :
    (∫ s in Ioo 0 t, F s) = (∫ s in Ioo 0 t, A s) +
      ∫ u in Ioo 0 t, ∫ s in Ioo 0 u, G u s := by
  calc
    _ = (∫ s in Ioo 0 t, A s) + ∫ s in Ioo 0 t, F s-A s := by
      rw [integral_sub hF hA]; ring
    _ = (∫ s in Ioo 0 t, A s) + ∫ s in Ioo 0 t, ∫ u in Ioo s t, G u s := by
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioo hp
    _ = _ := by rw [integral_swap G hG hB hb]

end TamingCompatibility.GeometricHilbert.TimeTriangle

namespace TamingCompatibility.GeometricHilbert.TimeTriangle
open _root_.MeasureTheory Set
lemma integral_shift (f : ℝ → ℝ) {s t : ℝ} (hst : s ≤ t) :
    (∫ u in Ioo s t, f (u-s)) = ∫ q in Ioo 0 (t-s), f q := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hst,
    intervalIntegral.integral_comp_sub_right,sub_self,
    intervalIntegral.integral_of_le (sub_nonneg.mpr hst),integral_Ioc_eq_integral_Ioo]
end TamingCompatibility.GeometricHilbert.TimeTriangle

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLeadingDuhamel
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma leading_test_duhamel
    (W : ℝ → X → FrameSpace A) (hW : StronglyMeasurable (Function.uncurry W))
    {V t : ℝ} (hV : 0 ≤ V) (_htp : 0 < t) (ht1 : t ≤ 1)
    (hWb : ∀ s ∈ Ioo 0 t, ∀ y, ‖W s y‖ ≤ V)
    (a : PreL2 A J α hs ht true) :
    (∫ s in Ioo 0 t, kernelInputTest A J α ht E (globalLeading J α ht A E) a.val (t-s) (W s)) =
      (∫ s in Ioo 0 t, ∫ y, framePairing A J α ht E a.val y (W s y) ∂geometricVolume A J α) +
        ∫ u in Ioo 0 t, ∫ s in Ioo 0 u,
          kernelInputTest A J α ht E (globalResidual J α ht A E) a.val (u-s) (W s) -
          kernelInputTest A J α ht E (globalLeading J α ht A E)
            (hodgeLaplacian A J α hs ht a).val (u-s) (W s) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  obtain ⟨BR,hBR,hRb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hR a.val a.property hV
  obtain ⟨BP,hBP,hPb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL a.val a.property hV
  obtain ⟨BD,hBD,hDb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hV
  have hPm := kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable a.val a.property W hW
  have hRm := kernelInputTest_shift_measurable A J α hs ht E hE _ hR.measurable a.val a.property W hW
  have hDm := kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property W hW
  have hAm : StronglyMeasurable (fun s => ∫ y, framePairing A J α ht E a.val y (W s y) ∂geometricVolume A J α) := by
    have hm : StronglyMeasurable (fun p : ℝ × X => framePairing A J α ht E a.val p.2 (W p.1 p.2)) :=
      (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
        (((framePairing_continuous A J α hs ht E hE a.val a.property).stronglyMeasurable.comp_measurable measurable_snd).prodMk hW)
    exact hm.integral_prod_right
  obtain ⟨B,hB,hφ⟩ := framePairing_bound A J α hs ht E hE a.val a.property
  apply TimeTriangle.integrated_primitive
  · apply Integrable.of_bound
      (hPm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable BP
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsp
    exact hPb (t-s) ⟨sub_pos.mpr hsp.2,(sub_le_self _ hsp.1.le).trans ht1⟩ (W s) (hWb s hsp)
  · apply Integrable.of_bound hAm.aestronglyMeasurable ((geometricVolume A J α).real univ*(B*V))
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hsp
    calc
      _ ≤ ∫ y : X, B*V ∂geometricVolume A J α := by
        apply norm_integral_le_of_norm_le (integrable_const _)
        exact Eventually.of_forall fun y => (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hφ y) (hWb s hsp y) (norm_nonneg _) hB)
      _ = _ := by simp [integral_const,smul_eq_mul]
  · exact hRm.sub hDm
  · exact add_nonneg hBR hBD
  · intro s hsp u hup
    have hp : u-s ∈ Ioc 0 1 := ⟨sub_pos.mpr hup.1,by linarith [hup.2,hsp.1]⟩
    exact (norm_sub_le _ _).trans (add_le_add (hRb _ hp (W s) (hWb s hsp))
      (hDb _ hp (W s) (hWb s hsp)))
  · intro s hsp
    rw [TimeTriangle.integral_shift (fun q =>
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val q (W s) -
      kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val q (W s)) hsp.2.le]
    exact (kernelInputTest_leading_primitive A J α hs ht E hE (W s)
      (hW.comp_measurable (measurable_const.prodMk measurable_id)) hV (hWb s hsp) a
      (sub_pos.mpr hsp.2) (by linarith [hsp.1])).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma leading_convolution_primitive
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C K)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (a : PreL2 A J α hs ht true)
    {t : ℝ} (htp : t ∈ Ioc 0 T) (ht1 : t ≤ 1) :
    kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K) a.val t v =
      (∫ s in Ioo 0 t, kernelInputTest A J α ht E K a.val s v) +
        ∫ u in Ioo 0 t,
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K) a.val u v -
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K)
            (hodgeLaplacian A J α hs ht a).val u v := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  let W := fun s => KernelL2.action (geometricVolume A J α) (K s) v
  have hW := KernelL2.time_action_measurable (geometricVolume A J α) K hK.measurable v hvm
  have hWb (s : ℝ) (hsp : s ∈ Ioc 0 T) (y : X) : ‖W s y‖ ≤ C*V := by
    have hi := hK.row_int s hsp y
    have hb := hK.row s hsp y
    simp only [VolterraBounds.weight,pow_zero,one_mul] at hi hb
    exact KernelL2.action_norm (geometricVolume A J α) (K s) v hV hv y hi hb
  have hCV := mul_nonneg hK.nonneg hV
  have hkt := hK.mono_time (geometricVolume A J α) htp.2
  have hlt := hL.mono_time (geometricVolume A J α) ht1
  have hrt := hR.mono_time (geometricVolume A J α) ht1
  have hh := leading_test_duhamel A J α hs ht E hE W hW hCV htp.1 ht1
    (fun s hp => hWb s ⟨hp.1,hp.2.le.trans htp.2⟩) a
  rw [kernelInputTest_convolution A J α hs ht E hE _ K hlt hkt a.val a.property
    ⟨htp.1,le_rfl⟩ v hvm hV hv]
  refine hh.trans ?_
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro s hp
    exact (kernelInputTest_action A J α hs ht E hE K hK a.val a.property
      ⟨hp.1,hp.2.le.trans htp.2⟩ v hvm hv).symm
  · apply setIntegral_congr_fun measurableSet_Ioo
    intro u hup
    obtain ⟨BR,_hBR,hRb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hR a.val a.property hCV
    obtain ⟨BD,_hBD,hDb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE _ hL
      (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property hCV
    have hiR : IntegrableOn (fun s => kernelInputTest A J α ht E (globalResidual J α ht A E) a.val (u-s) (W s)) (Ioo 0 u) := by
      apply Integrable.of_bound ((kernelInputTest_shift_measurable A J α hs ht E hE _ hR.measurable a.val a.property W hW).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable BR
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
      exact hRb (u-s) ⟨sub_pos.mpr hp.2,by linarith [hup.2,hp.1]⟩ (W s)
        (hWb s ⟨hp.1,hp.2.le.trans (hup.2.le.trans htp.2)⟩)
    have hiD : IntegrableOn (fun s => kernelInputTest A J α ht E (globalLeading J α ht A E)
        (hodgeLaplacian A J α hs ht a).val (u-s) (W s)) (Ioo 0 u) := by
      apply Integrable.of_bound ((kernelInputTest_shift_measurable A J α hs ht E hE _ hL.measurable
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property W hW).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable BD
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
      exact hDb (u-s) ⟨sub_pos.mpr hp.2,by linarith [hup.2,hp.1]⟩ (W s)
        (hWb s ⟨hp.1,hp.2.le.trans (hup.2.le.trans htp.2)⟩)
    dsimp only
    rw [integral_sub hiR hiD]
    rw [kernelInputTest_convolution A J α hs ht E hE _ K hrt hkt a.val a.property
      ⟨hup.1,hup.2.le⟩ v hvm hV hv,
      kernelInputTest_convolution A J α hs ht E hE _ K hlt hkt
        (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
        ⟨hup.1,hup.2.le⟩ v hvm hV hv]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeInputLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma kernelInputTest_time_integrable
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htT : t ≤ T)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) :
    IntegrableOn (fun s => kernelInputTest A J α ht E K a s v) (Ioo 0 t) := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨B,_hB,hb⟩ := kernelInputTest_uniform_bound A J α hs ht E hE K hK a ha hV
  apply Integrable.of_bound (kernelInputTest_time_measurable A J α hs ht E hE K hK.measurable a ha v hm).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
  exact hb s ⟨hp.1,hp.2.le.trans htT⟩ v hv

include hE in
omit [SecondCountableTopology X] in
lemma kernelInputTest_sum_zero
    (K L M : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {H B C T : ℝ} (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T H K)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T B L)
    (hM : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C M)
    (a : TwoForm X) (ha : IsSmooth a) {t : ℝ} (htp : t ∈ Ioc 0 T)
    (heq : ∀ x y, K t x y + L t x y + M t x y = 0)
    (v : X → FrameSpace A) (hm : StronglyMeasurable v) {V : ℝ} (hv : ∀ y, ‖v y‖ ≤ V) :
    kernelInputTest A J α ht E K a t v + kernelInputTest A J α ht E L a t v +
      kernelInputTest A J α ht E M a t v = 0 := by
  have hiK := kernelTestLinear_input_integrable A J α hs ht E hE K hK a ha htp v hm hv
  have hiL := kernelTestLinear_input_integrable A J α hs ht E hE L hL a ha htp v hm hv
  have hiM := kernelTestLinear_input_integrable A J α hs ht E hE M hM a ha htp v hm hv
  unfold kernelInputTest
  have hiKL : Integrable (fun y => kernelTestLinear A J α ht E K a t y (v y) +
      kernelTestLinear A J α ht E L a t y (v y)) (geometricVolume A J α) := hiK.add hiL
  rw [← integral_add hiK hiL,← integral_add hiKL hiM]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hK' := kernelTestLinear_integrable A J α hs ht E hE K hK a ha htp y
  have hL' := kernelTestLinear_integrable A J α hs ht E hE L hL a ha htp y
  have hM' := kernelTestLinear_integrable A J α hs ht E hE M hM a ha htp y
  have iK := hK'.apply_continuousLinearMap (v y)
  have iL := hL'.apply_continuousLinearMap (v y)
  have iM := hM'.apply_continuousLinearMap (v y)
  rw [kernelTestLinear_apply A J α hs ht E hE K hK a ha htp y (v y),
    kernelTestLinear_apply A J α hs ht E hE L hL a ha htp y (v y),
    kernelTestLinear_apply A J α hs ht E hE M hM a ha htp y (v y)]
  change (∫ x, framePairing A J α ht E a x (K t x y (v y)) ∂geometricVolume A J α) +
    (∫ x, framePairing A J α ht E a x (L t x y (v y)) ∂geometricVolume A J α) +
    (∫ x, framePairing A J α ht E a x (M t x y (v y)) ∂geometricVolume A J α) = 0
  change Integrable (fun x => framePairing A J α ht E a x (K t x y (v y))) _ at iK
  change Integrable (fun x => framePairing A J α ht E a x (L t x y (v y))) _ at iL
  change Integrable (fun x => framePairing A J α ht E a x (M t x y (v y))) _ at iM
  have iKL : Integrable (fun x => framePairing A J α ht E a x (K t x y (v y)) +
      framePairing A J α ht E a x (L t x y (v y))) (geometricVolume A J α) := iK.add iL
  rw [← integral_add iK iL,← integral_add iKL iM]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  rw [← map_add,← map_add]
  have hh := congrArg (fun F : FrameSpace A →L[ℝ] FrameSpace A => F (v y)) (heq x y)
  change K t x y (v y) + L t x y (v y) + M t x y (v y) = 0 at hh
  rw [hh,map_zero]
  rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma candidate_primitive_of_cancellation
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    {C T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hK : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C K)
    (heq : ∀ s ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E s x y + K s x y +
      VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K s x y = 0)
    (v : X → FrameSpace A) (hvm : StronglyMeasurable v) {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ y, ‖v y‖ ≤ V) (a : PreL2 A J α hs ht true)
    {t : ℝ} (htp : t ∈ Ioc 0 T) :
    kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v +
      kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K) a.val t v =
      (∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) -
        ∫ s in Ioo 0 t,
          kernelInputTest A J α ht E (globalLeading J α ht A E)
            (hodgeLaplacian A J α hs ht a).val s v +
          kernelInputTest A J α ht E
            (VolterraKernel.convolution (geometricVolume A J α) (globalLeading J α ht A E) K)
            (hodgeLaplacian A J α hs ht a).val s v := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A E hE 0 1
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A E hE 0 1
  have hRt := hR.mono_time (geometricVolume A J α) hT1
  have hLt := hL.mono_time (geometricVolume A J α) hT1
  have hRK := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ K hRt hK
  have hPK := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ K hLt hK
  have hRa := kernelInputTest_time_integrable A J α hs ht E hE _ hRt a.val a.property htp.2 v hvm hV hv
  have hKa := kernelInputTest_time_integrable A J α hs ht E hE K hK a.val a.property htp.2 v hvm hV hv
  have hRKa := kernelInputTest_time_integrable A J α hs ht E hE _ hRK a.val a.property htp.2 v hvm hV hv
  have hPD := kernelInputTest_time_integrable A J α hs ht E hE _ hLt
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property htp.2 v hvm hV hv
  have hPKD := kernelInputTest_time_integrable A J α hs ht E hE _ hPK
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property htp.2 v hvm hV hv
  have hpa := kernelInputTest_leading_primitive A J α hs ht E hE v hvm hV hv a htp.1 (htp.2.trans hT1)
  have hea := leading_convolution_primitive A J α hs ht E hE K hK v hvm hV hv a htp (htp.2.trans hT1)
  rw [integral_sub hRa hPD] at hpa
  rw [integral_sub hRKa hPKD] at hea
  have hsum : IntegrableOn (fun s =>
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v +
      kernelInputTest A J α ht E K a.val s v) (Ioo 0 t) := hRa.add hKa
  have hz : (∫ s in Ioo 0 t,
      kernelInputTest A J α ht E (globalResidual J α ht A E) a.val s v +
      kernelInputTest A J α ht E K a.val s v +
      kernelInputTest A J α ht E
        (VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E) K) a.val s v) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hp
    have hp' : s ∈ Ioc 0 T := ⟨hp.1,hp.2.le.trans htp.2⟩
    exact kernelInputTest_sum_zero A J α hs ht E hE _ K _ hRt hK hRK a.val a.property hp'
      (heq s hp') v hvm hv
  rw [integral_add hsum hRKa,integral_add hRa hKa] at hz
  rw [integral_add hPD hPKD]
  linarith

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCandidateEvolution
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma globalCandidate_evolution_of_bounds_oai {T L C : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (hcancel : ∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A E t x y +
      globalCorrection J α ht A E T t x y +
      VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A E)
        (globalCorrection J α ht A E T) t x y = 0)
    (v : X → FrameSpace A) (hv : Continuous v) :
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T)) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
        HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
          (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) := by
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨f,U,M,hM,hzero,hbound,hf,hpair,_hini⟩ :=
    globalCandidate_L2_of_bounds A J α hs ht E hE hT hL hC v hv
  have hErr := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL hC
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvb (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  have hp (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Ioc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ =
        kernelInputTest A J α ht E (globalLeading J α ht A E) a.val t v +
        kernelInputTest A J α ht E (globalError J α ht A E T) a.val t v := by
    rw [hpair a t htp]
    exact congrArg₂ (· + ·)
      (kernelInputTest_eq_weakAction A J α hs ht E hE _ hL a.val a.property htp v).symm
      (kernelInputTest_eq_weakAction A J α hs ht E hE _ hErr a.val a.property htp v).symm
  have hi (a : PreL2 A J α hs ht true) :
      IntegrableOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    have hP := kernelInputTest_time_integrable A J α hs ht E hE _ hL a.val a.property
      le_rfl v hv.stronglyMeasurable hV hvb
    have hQ := kernelInputTest_time_integrable A J α hs ht E hE _ hErr a.val a.property
      le_rfl v hv.stronglyMeasurable hV hvb
    apply (hP.add hQ).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htp
    exact (hp a t ⟨htp.1,htp.2.le⟩).symm
  have hprim (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Icc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ = ⟪f,smoothL2 A J α hs ht true a⟫ -
        ∫ s in Ioo 0 t, ⟪U s,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ := by
    by_cases hz : t=0
    · simp [hz,hzero]
    have htpos : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne htp.1 (Ne.symm hz),htp.2⟩
    rw [hp a t htpos,hf a]
    have hh := candidate_primitive_of_cancellation A J α hs ht E hE
      (globalCorrection J α ht A E T) hT hT1 hC hcancel
      v hv.stronglyMeasurable hV hvb a htpos
    apply hh.trans
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hsp
    exact (hp (hodgeLaplacian A J α hs ht a) s ⟨hsp.1,hsp.2.le.trans htp.2⟩).symm
  obtain ⟨hc,hd⟩ := WeakHeat.of_primitive (hodgeLaplacian A J α hs ht)
    (fun a t => ⟪U t,smoothL2 A J α hs ht true a⟫)
    (fun a => ⟪f,smoothL2 A J α hs ht true a⟫) hT.le hi hprim
  exact ⟨f,U,M,hM,hzero,hbound,hf,hpair,hc,hd⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.globalCandidate_evolution_of_bounds_oai.{u_1}
