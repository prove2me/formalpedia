-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:18.238553+00:00
-- url     : https://prove2.me/submissions/8afab8c7-0616-40a7-a323-bc0127b0d2bf

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_ProductSamplingPhaseMoments_expected_average_error_le_source_scale

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarEndpointDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarEndpointDensity

theorem endpointMap_left (t : ℝ) {z : ℝ} (hz : z ≤ 1 / 2) :
    endpointMap t z = (1 + t) * z := by
  unfold endpointMap cutDistance
  rw [min_eq_left (by linarith)]
  ring

theorem endpointMap_right (t : ℝ) {z : ℝ} (hz : 1 / 2 ≤ z) :
    endpointMap t z = (1 - t) * z + t := by
  unfold endpointMap cutDistance
  rw [min_eq_right (by linarith)]
  ring

theorem continuous_endpointMap (t : ℝ) : Continuous (endpointMap t) := by
  unfold endpointMap cutDistance
  fun_prop

theorem midpoint_pos {t : ℝ} (ht0 : 0 ≤ t) : 0 < midpoint t := by
  unfold midpoint
  linarith

theorem midpoint_lt_one {t : ℝ} (ht1 : t < 1) : midpoint t < 1 := by
  unfold midpoint
  linarith

theorem slopeDensity_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    0 < slopeDensity t s := by
  unfold slopeDensity
  split_ifs <;> positivity

theorem slopeDensity_upper {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    slopeDensity t s ≤ (1 - t)⁻¹ := by
  unfold slopeDensity
  split_ifs
  · apply inv_anti₀ (by linarith)
    linarith
  · exact le_rfl

theorem slopeDensity_mul_intervalIntegrable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun s => φ s * slopeDensity t s) volume 0 1 := by
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hleft : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := by
    have hi : IntervalIntegrable (fun s => φ s * (1 + t)⁻¹)
        volume 0 (midpoint t) := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm0.le] at hs
    simp only [slopeDensity, ite_eq_left hs.2.le]
  have hright : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := by
    have hi : IntervalIntegrable (fun s => φ s * (1 - t)⁻¹)
        volume (midpoint t) 1 := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm1.le] at hs
    simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
  exact hleft.trans hright

theorem endpointMap_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ z in (0 : ℝ)..1, φ (endpointMap t z)) =
      ∫ s in (0 : ℝ)..1, φ s * slopeDensity t s := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hn : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hc : Continuous (fun z => φ (endpointMap t z)) :=
    hφ.comp (continuous_endpointMap t)
  have hleft : (∫ z in (0 : ℝ)..(1 / 2), φ (endpointMap t z)) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ z in (0 : ℝ)..(1 / 2), φ ((1 + t) * z) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_left t hz.2.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_left φ hp]
        simp only [mul_zero, smul_eq_mul]
        congr 2
        unfold midpoint
        ring
  have hright : (∫ z in (1 / 2 : ℝ)..1, φ (endpointMap t z)) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ z in (1 / 2 : ℝ)..1, φ ((1 - t) * z + t) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_right t hz.1.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_add φ hn t]
        simp only [smul_eq_mul]
        congr 2
        · unfold midpoint
          ring
        · ring
  have hd := slopeDensity_mul_intervalIntegrable ht0 ht1 hφ
  have hdleft : (∫ s in (0 : ℝ)..midpoint t, φ s * slopeDensity t s) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ s in (0 : ℝ)..midpoint t, φ s * (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm0.le
        intro s hs
        simp only [slopeDensity, ite_eq_left hs.2.le]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  have hdright : (∫ s in midpoint t..(1 : ℝ), φ s * slopeDensity t s) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ s in midpoint t..(1 : ℝ), φ s * (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm1.le
        intro s hs
        simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), hleft, hright]
  have hdl : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := hd.mono_set (by
    rw [uIcc_of_le hm0.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hm1.le)
  have hdr : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := hd.mono_set (by
    rw [uIcc_of_le hm1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hm0.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr]
  rw [hdleft, hdright]

theorem integral_slopeDensity {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s in (0 : ℝ)..1, slopeDensity t s) = 1 := by
  have h := endpointMap_integral ht0 ht1 (φ := fun _ => 1) continuous_const
  simpa using h.symm

theorem slopeDensity_deviation {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) :
    |slopeDensity t s - 1| ≤ h / (1 - h) := by
  have ht1 : t < 1 := lt_of_le_of_lt hth hh1
  have hh0 : 0 ≤ h := le_trans ht0 hth
  have hp : 0 < 1 + t := by linarith
  have hn : 0 < 1 - t := by linarith
  have hd : 0 < 1 - h := by linarith
  unfold slopeDensity
  split_ifs
  · have heq : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg ht0 hp.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)
  · have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp
      ring
    rw [heq, abs_of_nonneg (div_nonneg ht0 hn.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)

theorem slopeDensity_uniform_upper {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) : slopeDensity t s ≤ (1 - h)⁻¹ := by
  apply (slopeDensity_upper ht0 (lt_of_le_of_lt hth hh1) s).trans
  exact inv_anti₀ (by linarith) (by linarith)

theorem measurable_slopeDensity : Measurable (fun p : ℝ × ℝ => slopeDensity p.1 p.2) := by
  unfold slopeDensity midpoint
  apply Measurable.ite
  · exact measurableSet_le measurable_snd
      ((measurable_const.add measurable_fst).div_const 2)
  · exact (measurable_const.add measurable_fst).inv
  · exact (measurable_const.sub measurable_fst).inv

theorem slopeDensity_parameter_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1)
    (s : ℝ) : IntervalIntegrable (fun t => slopeDensity t s) volume 0 h := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le hh0]; exact measure_Ioc_lt_top)
    ((measurable_slopeDensity.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity t s‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) s)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 s

theorem averagedDensity_nonneg {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    0 ≤ averagedDensity h s := by
  unfold averagedDensity
  apply mul_nonneg (inv_nonneg.mpr hh0.le)
  apply intervalIntegral.integral_nonneg hh0.le
  intro t ht
  exact (slopeDensity_pos ht.1 (lt_of_le_of_lt ht.2 hh1) s).le

theorem averagedDensity_upper {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    averagedDensity h s ≤ (1 - h)⁻¹ := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have hb : (∫ t in (0 : ℝ)..h, slopeDensity t s) ≤ h * (1 - h)⁻¹ := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..h, (1 - h)⁻¹ :=
        intervalIntegral.integral_mono_on hh0.le hint intervalIntegrable_const
          (fun t ht => slopeDensity_uniform_upper ht.1 ht.2 hh1 s)
      _ = _ := by simp
  unfold averagedDensity
  calc
    _ ≤ h⁻¹ * (h * (1 - h)⁻¹) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh0.ne', one_mul]

theorem averagedDensity_deviation {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    |averagedDensity h s - 1| ≤ h / (1 - h) := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have heq : averagedDensity h s - 1 =
      h⁻¹ * ∫ t in (0 : ℝ)..h, (slopeDensity t s - 1) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    unfold averagedDensity
    rw [mul_sub, inv_mul_cancel₀ hh0.ne']
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hh0)]
  have hb : |∫ t in (0 : ℝ)..h, (slopeDensity t s - 1)| ≤
      (h / (1 - h)) * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h) (C := h / (1 - h))
      (f := fun t => slopeDensity t s - 1) (by
        intro t ht
        rw [uIoc_of_le hh0.le] at ht
        simpa only [Real.norm_eq_abs] using slopeDensity_deviation ht.1.le ht.2 hh1 s)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hh0] using this
  calc
    _ ≤ h⁻¹ * ((h / (1 - h)) * h) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by field_simp

theorem slopeDensity_rectangle_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) :
    IntegrableOn (Function.uncurry slopeDensity)
      (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  apply IntegrableOn.of_bound hfinite measurable_slopeDensity.aestronglyMeasurable ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  have ht := hp.1
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity p.1 p.2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) p.2)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 p.2

theorem averagedDensity_intervalIntegrable {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    IntervalIntegrable (averagedDensity h) volume 0 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hr
  have hi := hr.integral_prod_right.const_mul h⁻¹
  rw [intervalIntegrable_iff]
  change Integrable (fun s => h⁻¹ * ∫ t in (0 : ℝ)..h, slopeDensity t s)
    (volume.restrict (uIoc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le hh0.le,
    uIoc_of_le hh0.le, Function.uncurry] using hi

theorem integral_averagedDensity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, averagedDensity h s) = 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  have hi : (∫ t in (0 : ℝ)..h, ∫ s in (0 : ℝ)..1, slopeDensity t s) = h := by
    calc
      _ = ∫ _t in (0 : ℝ)..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
        intro t ht
        exact integral_slopeDensity ht.1.le (lt_trans ht.2 hh1)
      _ = _ := by simp
  unfold averagedDensity
  rw [intervalIntegral.integral_const_mul,
    ← intervalIntegral_intervalIntegral_swap hr, hi, inv_mul_cancel₀ hh0.ne']

theorem unitMass_square_identity {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) =
      1 + ∫ s in (0 : ℝ)..1, (f s - 1) ^ 2 := by
  have hdev : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  have hfun : (fun s => (f s) ^ 2) =
      (fun s => (f s - 1) ^ 2 + 2 * f s - 1) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_sub (hdev.add (hf.const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_add hdev (hf.const_mul 2), intervalIntegral.integral_const_mul, hmass]
  simp
  ring

theorem unitMass_square_le {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) ≤ 1 + δ ^ 2 := by
  rw [unitMass_square_identity hf hδ hbound hmass]
  apply add_le_add le_rfl
  have hint : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  calc
    _ ≤ ∫ _s in (0 : ℝ)..1, δ ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
        (fun s hs => by
          have hb := hbound s hs
          exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb))
    _ = _ := by simp

theorem averagedDensity_second_moment {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, (averagedDensity h s) ^ 2) ≤
      1 + h ^ 2 / (1 - h) ^ 2 := by
  have hb := unitMass_square_le (averagedDensity_intervalIntegrable hh0 hh1)
    (show 0 ≤ h / (1 - h) by positivity)
    (fun s _ => averagedDensity_deviation hh0 hh1 s)
    (integral_averagedDensity hh0 hh1)
  simpa only [div_pow] using hb

end Invariant233.ScalarEndpointDensity

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSampling
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma delta_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ delta s := by
  exact le_min hs.1 (sub_nonneg.mpr hs.2)

lemma delta_le_half (s : ℝ) : delta s ≤ 1 / 2 := by
  unfold delta
  rcases le_total s (1 / 2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

lemma cutoff_iff {α s : ℝ} : α ≤ delta s ↔ s ∈ Icc α (1 - α) := by
  simp only [delta, le_min_iff, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma rawKernel_nonneg {h α s t : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ rawKernel h α s t := by
  unfold rawKernel
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh (delta_nonneg hs))) _
  · exact le_rfl

lemma integral_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t) = if α ≤ delta s then 1 else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    exact mul_inv_cancel₀ hd.ne'
  · simp

lemma integral_sq_rawKernel (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    (∫ t : ℝ, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  unfold rawKernel
  split_ifs with hs
  · have hd : 0 < h * delta s := mul_pos hh (hα.trans_le hs)
    have heq : (fun t : ℝ => ((Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) t)^2) =
        (Ioo 0 (h * delta s)).indicator (fun _ => ((h * delta s)⁻¹)^2) := by
      funext t
      by_cases ht : t ∈ Ioo 0 (h * delta s) <;> simp [ht]
    rw [heq, integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le hd.le]
    simp only [sub_zero, smul_eq_mul]
    field_simp
  · simp

lemma rawKernel_eq_zero_of_not_mem_unit {h α s t : ℝ}
    (_hh : 0 ≤ h) (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∉ Ioc (0 : ℝ) 1) : rawKernel h α s t = 0 := by
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht'
    apply ht
    refine ⟨ht'.1, ht'.2.le.trans ?_⟩
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  · rfl

theorem interval_integral_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t) =
      if α ≤ delta s then 1 else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht)]
  exact integral_rawKernel h α s hh hα

theorem interval_integral_sq_rawKernel {h α s : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      if α ≤ delta s then (h * delta s)⁻¹ else 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => by rw [rawKernel_eq_zero_of_not_mem_unit hh.le hhone hs ht]; norm_num)]
  exact integral_sq_rawKernel h α s hh hα

theorem integral_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t) = 1 - 2 * α := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t) =
      (Icc α (1 - α)).indicator (fun _ => (1 : ℝ)) := by
    funext s
    rw [integral_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith : α ≤ 1 - α)]
    simp only [smul_eq_mul, mul_one]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem integral_inv_delta {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in α..(1 - α), (delta s)⁻¹) =
      2 * Real.log (1 / (2 * α)) := by
  have hab : α ≤ 1 - α := by linarith
  have hmid : (1 / 2 : ℝ) ≤ 1 - α := by linarith
  have hd : Continuous (fun s : ℝ => delta s) :=
    continuous_id.min (continuous_const.sub continuous_id)
  have hfi : IntervalIntegrable (fun s : ℝ => (delta s)⁻¹) volume α (1 - α) := by
    apply intervalIntegral.intervalIntegrable_inv _ hd.continuousOn
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ne_of_gt (hα.trans_le (cutoff_iff.mpr hs))
  have hleft := hfi.mono_set (show uIcc α (1 / 2 : ℝ) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hαhalf, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hmid)
  have hright := hfi.mono_set (show uIcc (1 / 2 : ℝ) (1 - α) ⊆ uIcc α (1 - α) by
    rw [uIcc_of_le hmid, uIcc_of_le hab]
    exact Icc_subset_Icc hαhalf le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hleftEq : (∫ s in α..(1 / 2 : ℝ), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hαhalf] at hs
    change (min s (1 - s))⁻¹ = s⁻¹
    rw [min_eq_left (by linarith [hs.2] : s ≤ 1 - s)]
  have hrightEq : (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
      ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
    calc
      (∫ s in (1 / 2 : ℝ)..(1 - α), (delta s)⁻¹) =
          ∫ s in (1 / 2 : ℝ)..(1 - α), (1 - s)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hmid] at hs
        change (min s (1 - s))⁻¹ = (1 - s)⁻¹
        rw [min_eq_right (by linarith [hs.1] : 1 - s ≤ s)]
      _ = ∫ s in α..(1 / 2 : ℝ), s⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s⁻¹) 1]
        congr 1 <;> ring
  rw [hleftEq, hrightEq, integral_inv_of_pos hα (by norm_num : (0 : ℝ) < 1 / 2)]
  have heq : (1 / 2 : ℝ) / α = 1 / (2 * α) := by ring
  rw [heq]
  ring

theorem integral_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have heq : (fun s : ℝ => ∫ t : ℝ, rawKernel h α s t ^ 2) =
      (Icc α (1 - α)).indicator (fun s => (h * delta s)⁻¹) := by
    funext s
    rw [integral_sq_rawKernel h α s hh hα]
    simp only [cutoff_iff, Set.indicator_apply]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : α ≤ 1 - α)]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_delta hα hαhalf]
    ring
  · intro s hs
    apply Set.indicator_of_notMem
    intro hs'
    apply hs
    exact ⟨hα.le.trans hs'.1, hs'.2.trans (by linarith)⟩

theorem double_interval_integral_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) = 1 - 2 * α := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_rawKernel hh hhone hα hs, integral_rawKernel h α s hh hα]
    _ = 1 - 2 * α := integral_integral_rawKernel hh hα hαhalf

theorem double_interval_integral_sq_rawKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, rawKernel h α s t ^ 2) =
        ∫ s in Icc (0 : ℝ) 1, ∫ t : ℝ, rawKernel h α s t ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [interval_integral_sq_rawKernel hh hhone hα hs,
        integral_sq_rawKernel h α s hh hα]
    _ = (2 / h) * Real.log (1 / (2 * α)) := integral_integral_sq_rawKernel hh hα hαhalf

theorem interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
      if α ≤ delta (Int.fract z) then 1 else 0 := by
  calc
    (∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ v in (0 : ℝ)..1, rawKernel h α (Int.fract z) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = if α ≤ delta (Int.fract z) then 1 else 0 :=
      interval_integral_rawKernel hh hhone hα
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem double_interval_integral_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) = 1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = 1 - 2 * α := double_interval_integral_rawKernel hh hhone hα hαhalf

theorem double_interval_integral_sq_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  calc
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v ^ 2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, rawKernel h α z v ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro z hz
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro v hv
      simp only [circleKernel, Int.fract_eq_self.mpr ⟨hz.1.le, hz.2⟩,
        Int.fract_eq_self.mpr ⟨hv.1.le, hv.2⟩]
    _ = (2 / h) * Real.log (1 / (2 * α)) :=
      double_interval_integral_sq_rawKernel hh hhone hα hαhalf

theorem averaged_circleKernel_bounds {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (z : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α z v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α z v) ≤ 1 := by
  rw [interval_integral_circleKernel hh hhone hα z]
  split_ifs <;> norm_num

theorem integral_sq_averaged_circleKernel {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
      1 - 2 * α := by
  calc
    (∫ z in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α z v)^2) =
        ∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α z v := by
      apply intervalIntegral.integral_congr
      intro z _
      dsimp only
      rw [interval_integral_circleKernel hh hhone hα z]
      split_ifs <;> norm_num
    _ = 1 - 2 * α := double_interval_integral_circleKernel hh hhone hα hαhalf

lemma manuscript_parameters {m : ℕ} (hm : 200 ≤ m) :
    0 < (m : ℝ) ^ (-(3 / 5 : ℝ)) ∧
      (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 ∧
      0 < 1 / (m : ℝ)^2 ∧ 1 / (m : ℝ)^2 ≤ 1 / 2 := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  refine ⟨Real.rpow_pos_of_pos hmp _,
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num),
    one_div_pos.mpr (sq_pos_of_pos hmp), ?_⟩
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by nlinarith)

theorem manuscriptKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    double_interval_integral_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptKernel, heq] using
    double_interval_integral_sq_circleKernel hh hhone hα hαhalf

lemma triangularKernel_sq (s t : ℝ) : triangularKernel s t ^ 2 = triangularKernel s t := by
  unfold triangularKernel
  by_cases ht : t ∈ Ioo 0 (1 - s) <;> simp [ht]

theorem interval_integral_triangularKernel {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, triangularKernel s t) = 1 - s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · unfold triangularKernel
    rw [integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le (sub_nonneg.mpr hs.2)]
    simp
  · intro t ht
    unfold triangularKernel
    apply Set.indicator_of_notMem
    intro ht'
    apply ht
    exact ⟨ht'.1, ht'.2.le.trans (by linarith [hs.1])⟩

theorem triangularKernel_mass :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t) = 1 / 2 := by
  calc
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t) =
        ∫ s in (0 : ℝ)..1, (1 - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact interval_integral_triangularKernel hs
    _ = 1 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        intervalIntegral.intervalIntegrable_id]
      norm_num

theorem triangularKernel_secondMoment :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, triangularKernel s t ^ 2) = 1 / 2 := by
  simp_rw [triangularKernel_sq]
  exact triangularKernel_mass

theorem triangularKernel_averaged_secondMoment :
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, triangularKernel s t)^2) = 1 / 3 := by
  calc
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, triangularKernel s t)^2) =
        ∫ s in (0 : ℝ)..1, (1 - s)^2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      dsimp only
      rw [interval_integral_triangularKernel hs]
    _ = ∫ s in (0 : ℝ)..1, s^2 := by
      simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left (fun s : ℝ => s^2)
        (a := 0) (b := 1) 1
    _ = 1 / 3 := by norm_num

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointKernelGeometry
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem rawKernel_uncut_zero_of_nonpos {h x v : ℝ} (hh : 0 ≤ h)
    (hx : x ≤ 0) (_hv : 0 ≤ v) : rawKernel h 0 x v = 0 := by
  unfold rawKernel
  split_ifs with hd
  · apply Set.indicator_of_notMem
    intro hmem
    have hdelta : delta x ≤ 0 := (min_le_left _ _).trans hx
    have : h * delta x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh hdelta
    linarith [hmem.1, hmem.2]
  · rfl

theorem uncut_endpoint_no_wrap {h s v : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    circleKernel h 0 (s - v) v = rawKernel h 0 (s - v) v := by
  unfold circleKernel
  rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  by_cases hvs : v ≤ s
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  · have hsv : s < v := lt_of_not_ge hvs
    rw [rawKernel_uncut_zero_of_nonpos (x := s - v) hh0 (by linarith) hv0.le]
    have hfloor : ⌊s - v⌋ = -1 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith
    have hfract : Int.fract (s - v) = s - v + 1 := by
      rw [Int.fract, hfloor]
      norm_num
    rw [hfract]
    unfold rawKernel
    split_ifs
    · apply Set.indicator_of_notMem
      intro hmem
      have hdelta0 : 0 ≤ delta (s - v + 1) := by
        apply delta_nonneg
        constructor <;> linarith
      have hdelta : delta (s - v + 1) ≤ v - s := by
        unfold delta
        exact (min_le_right _ _).trans (by linarith)
      have hmul : h * delta (s - v + 1) ≤ delta (s - v + 1) :=
        (mul_le_mul_of_nonneg_right hh1 hdelta0).trans_eq (one_mul _)
      linarith [hmem.2]
    · rfl

theorem rawKernel_le_uncut {h α s v : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : rawKernel h α s v ≤ rawKernel h 0 s v := by
  have hd : 0 ≤ delta s := delta_nonneg hs
  unfold rawKernel
  rw [ite_eq_left hd]
  split_ifs
  · exact le_rfl
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh hd)) _

theorem uncut_endpoint_left_formula {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have heq : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hineq <;> nlinarith
  by_cases hv : 0 < v
  · have hd : delta (s - v) = s - v := by
      unfold delta
      rw [min_eq_left (by linarith)]
    unfold rawKernel
    rw [hd]
    by_cases hvs : v < h * s / (1 + h)
    · have hvbound : v < s := by
        have := heq.mpr hvs
        nlinarith
      simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply, mem_Ioo,
        hv, heq.mpr hvs, hvs, and_self, ite_true, if_true]
    · have hvnot : ¬ v < h * (s - v) := fun h => hvs (heq.mp h)
      simp only [Set.indicator_apply, mem_Ioo, hv, hvnot, hvs, and_false, ite_false, if_false,
        ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, if_false, ite_self]

theorem integral_uncut_endpoint_left {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  have hL0 : 0 < h * s / (1 + h) := div_pos (mul_pos hh0 hs0) hp
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) := by
    funext v
    exact uncut_endpoint_left_formula hh0 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    simp only [sub_zero]
    rw [integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h)) hs0]
    have hratio : s / (s - h * s / (1 + h)) = 1 + h := by
      field_simp
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hL1.le⟩

theorem averagedDensity_left_formula {h s : ℝ} (hh0 : 0 < h) (hs1 : s ≤ 1 / 2) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 + t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.1])]
    _ = Real.log (1 + h) := by
      rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
      simp only [add_zero]
      rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hp]
      simp

theorem integral_uncut_circleEndpoint_left {h s : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_left_formula hh0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1 hs0 (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_left hh0 hs0 hs1

theorem uncut_endpoint_right_formula {h s : ℝ} (hh0 : 0 < h) (_hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hR : h * (1 - s) / (1 - h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hn]
    nlinarith
  have hL : h * s / (1 + h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hp]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioo, heqR]
    · have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      have hvR : ¬v < h * (1 - s) / (1 - h) := by linarith
      have hvL : ¬v < h * (s - v) := by
        rw [heqL]
        linarith
      unfold rawKernel
      rw [hd]
      simp only [Set.indicator_apply, mem_Ioo, hvR, hvL, and_false, ite_false, if_false, ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, if_false, ite_self]

theorem integral_uncut_endpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 - h)⁻¹) := by
  have hn : 0 < 1 - h := by linarith
  have hR0 : 0 < h * (1 - s) / (1 - h) := div_pos (mul_pos hh0 (by linarith)) hn
  have hR1 : h * (1 - s) / (1 - h) < 1 := by
    rw [div_lt_iff₀ hn]
    nlinarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) := by
    funext v
    exact uncut_endpoint_right_formula hh0 hh1 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s)
      (by linarith : 0 < 1 - s + h * (1 - s) / (1 - h))]
    have hratio : (1 - s + h * (1 - s) / (1 - h)) / (1 - s) = (1 - h)⁻¹ := by
      field_simp [ne_of_gt (show 0 < 1 - s by linarith), hn.ne']
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hR1.le⟩

theorem averagedDensity_right_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log ((1 - h)⁻¹) := by
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 - t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.2])]
    _ = Real.log ((1 - h)⁻¹) := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
      simp only [sub_zero]
      rw [integral_inv_of_pos (by linarith : 0 < 1 - h) (by norm_num : (0 : ℝ) < 1)]
      simp only [one_div]

theorem integral_uncut_circleEndpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_right_formula hh0 hh1 hs0]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) hs1 hv.1 hv.2
    _ = _ := integral_uncut_endpoint_right hh0 hh1 hs0 hs1

theorem uncut_endpoint_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹) v +
      (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
        (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hsunit : s < 1 := by linarith
  have hR : s - 1 / 2 < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      have hvR : v < h * (1 - s + v) := heqR.mpr (lt_of_le_of_lt hvb hR)
      have hvnot : ¬ s - 1 / 2 < v := not_lt_of_ge hvb
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvR, hvnot,
        and_self, false_and, ite_true, if_true, ite_false, if_false, add_zero]
    · have hvb' : s - 1 / 2 < v := lt_of_not_ge hvb
      have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      unfold rawKernel
      rw [hd]
      by_cases hvL : v < h * s / (1 + h)
      · have hvs : v < s := by
          have := heqL.mpr hvL
          nlinarith
        simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply,
          mem_Ioc, mem_Ioo, hv, hvb, hvb', hvL, heqL.mpr hvL,
          and_self, and_false, ite_true, if_true, ite_false, if_false, zero_add]
      · have hvnot : ¬v < h * (s - v) := fun hh => hvL (heqL.mp hh)
        simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvL, hvnot,
          and_false, ite_false, if_false, ite_self, add_zero]
  · have hvb : ¬s - 1 / 2 < v := by linarith
    unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb,
      false_and, ite_false, if_false, ite_self, add_zero]

theorem integral_uncut_endpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hB0 : 0 < s - 1 / 2 := by linarith
  have hL : s - 1 / 2 < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    nlinarith
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hB1 : s - 1 / 2 < 1 := by linarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  let fR : ℝ → ℝ := (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹)
  let fL : ℝ → ℝ := (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
    (fun v => (h * (s - v))⁻¹)
  have hfR : Integrable fR := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.1]))
  have hfL : Integrable fL := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.2]))
  have hfun : (fun v => rawKernel h 0 (s - v) v) = fun v => fR v + fL v := by
    funext v
    exact uncut_endpoint_middle_formula hh0 hh1 hs0 hs1 v
  have hRint : (∫ v, fR v) = h⁻¹ * Real.log ((1 / 2) / (1 - s)) := by
    dsimp only [fR]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hB0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    have hb : 1 - s + (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s) (by norm_num : (0 : ℝ) < 1 / 2)]
  have hLint : (∫ v, fL v) = h⁻¹ * Real.log ((1 / 2) / (s - h * s / (1 + h))) := by
    dsimp only [fL]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    have hb : s - (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb, integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h))
      (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_add hfR hfL, hRint, hLint, ← mul_add,
      ← Real.log_mul (by positivity) (by positivity)]
    congr 2
    field_simp [ne_of_gt (show 0 < 1 - s by linarith), hspos.ne', hp.ne']
    ring
  · intro v hv
    have hnotR : v ∉ Ioc 0 (s - 1 / 2) :=
      fun ht => hv ⟨ht.1, ht.2.trans hB1.le⟩
    have hnotL : v ∉ Ioo (s - 1 / 2) (h * s / (1 + h)) :=
      fun ht => hv ⟨lt_trans hB0 ht.1, ht.2.le.trans hL1.le⟩
    simp only [fR, fL, Set.indicator_of_notMem hnotR, Set.indicator_of_notMem hnotL, add_zero]

theorem averagedDensity_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    ScalarEndpointDensity.averagedDensity h s =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hC0 : 0 < 2 * s - 1 := by linarith
  have hCh : 2 * s - 1 < h := by linarith
  have hC1 : 2 * s - 1 < 1 := by linarith
  have hd := ScalarEndpointDensity.slopeDensity_parameter_integrable hh0.le hh1 s
  have hdl : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume 0 (2 * s - 1) := hd.mono_set (by
    rw [uIcc_of_le hC0.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc le_rfl hCh.le)
  have hdr : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume (2 * s - 1) h := hd.mono_set (by
    rw [uIcc_of_le hCh.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc hC0.le le_rfl)
  have hleft : (∫ t in (0 : ℝ)..(2 * s - 1), ScalarEndpointDensity.slopeDensity t s) =
      Real.log (1 / (1 - (2 * s - 1))) := by
    calc
      _ = ∫ t in (0 : ℝ)..(2 * s - 1), (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hC0.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.2])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
        simp only [sub_zero]
        rw [integral_inv_of_pos (by linarith : 0 < 1 - (2 * s - 1))
          (by norm_num : (0 : ℝ) < 1)]
  have hright : (∫ t in (2 * s - 1)..h, ScalarEndpointDensity.slopeDensity t s) =
      Real.log ((1 + h) / (1 + (2 * s - 1))) := by
    calc
      _ = ∫ t in (2 * s - 1)..h, (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hCh.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.1])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
        rw [integral_inv_of_pos (by linarith : 0 < 1 + (2 * s - 1)) hp]
  unfold ScalarEndpointDensity.averagedDensity
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr, hleft, hright,
    ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  field_simp [hspos.ne', ne_of_gt (show 0 < 1 - s by linarith),
    ne_of_gt (show 0 < 1 - (2 * s - 1) by linarith),
    ne_of_gt (show 0 < 1 + (2 * s - 1) by linarith),
    show (2 : ℝ) - s * 2 ≠ 0 by linarith]
  ring

theorem integral_uncut_circleEndpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_middle_formula hh0 hh1 hs0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_middle hh0 hh1 hs0 hs1

theorem integral_uncut_circleEndpoint {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  by_cases hleft : s ≤ 1 / 2
  · exact integral_uncut_circleEndpoint_left hh0 hh1.le hs0 hleft
  · by_cases hright : (1 + h) / 2 ≤ s
    · exact integral_uncut_circleEndpoint_right hh0 hh1 hright hs1
    · exact integral_uncut_circleEndpoint_middle hh0 hh1 (lt_of_not_ge hleft) (lt_of_not_ge hright)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarEndpointKernelBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem measurable_rawKernel_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => rawKernel h α p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => delta p.1) :=
    (continuous_fst.min (continuous_const.sub continuous_fst)).measurable
  unfold rawKernel
  simp only [Set.indicator_apply, mem_Ioo]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.mul hd)))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

theorem measurable_circleEndpoint_pair (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1 - p.2) p.2) := by
  exact (measurable_rawKernel_pair h α).comp
    (((measurable_fst.sub measurable_snd).fract).prodMk measurable_snd.fract)

theorem rawKernel_height {h α s v : ℝ} (hh : 0 < h) (hα : 0 < α) :
    0 ≤ rawKernel h α s v ∧ rawKernel h α s v ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hd
  · by_cases hv : v ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem hv]
      have hp : 0 < h * delta s := mul_pos hh (hα.trans_le hd)
      exact ⟨(inv_pos.mpr hp).le, inv_anti₀ (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hd hh.le)⟩
    · rw [Set.indicator_of_notMem hv]
      exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩
  · exact ⟨le_rfl, (inv_pos.mpr (mul_pos hh hα)).le⟩

theorem circleEndpoint_intervalIntegrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (s : ℝ) : IntervalIntegrable (fun v => circleKernel h α (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_circleEndpoint_pair h α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable ((h * α)⁻¹)
  apply Filter.Eventually.of_forall
  intro v
  change ‖circleKernel h α (s - v) v‖ ≤ _
  unfold circleKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (rawKernel_height hh hα).1]
  exact (rawKernel_height hh hα).2

theorem delta_backward_bound {s v : ℝ} (hv : 0 ≤ v) : delta s ≤ delta (s - v) + v := by
  have heq : delta (s - v) + v = min s (1 - s + 2 * v) := by
    unfold delta
    rw [← min_add_add_right]
    congr 1 <;> ring
  rw [heq]
  exact min_le_min le_rfl (by linarith)

theorem uncut_rawEndpoint_height {h s v : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) (hv : 0 ≤ v) :
    0 ≤ rawKernel h 0 (s - v) v ∧
      rawKernel h 0 (s - v) v ≤ (1 + h) / (h * delta s) := by
  have hdS : 0 < delta s := lt_min hs0 (by linarith)
  have hC : 0 ≤ (1 + h) / (h * delta s) := by positivity
  unfold rawKernel
  split_ifs with hd
  · by_cases hmem : v ∈ Ioo 0 (h * delta (s - v))
    · rw [Set.indicator_of_mem hmem]
      have hdpos : 0 < delta (s - v) := by
        have hp : 0 < h * delta (s - v) := lt_trans hmem.1 hmem.2
        exact (mul_pos_iff_of_pos_left hh).mp hp
      refine ⟨(inv_pos.mpr (mul_pos hh hdpos)).le, ?_⟩
      have hcomp : delta s ≤ (1 + h) * delta (s - v) := by
        have := delta_backward_bound (s := s) hv
        linarith [hmem.2]
      rw [inv_eq_one_div, div_le_div_iff₀ (mul_pos hh hdpos) (mul_pos hh hdS)]
      nlinarith [mul_le_mul_of_nonneg_left hcomp hh.le]
    · rw [Set.indicator_of_notMem hmem]
      exact ⟨le_rfl, hC⟩
  · exact ⟨le_rfl, hC⟩

theorem uncut_rawEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => rawKernel h 0 (s - v) v) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((measurable_rawKernel_pair h 0).comp
      ((measurable_const.sub measurable_id).prodMk measurable_id)).aestronglyMeasurable
    ((1 + h) / (h * delta s))
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  change ‖rawKernel h 0 (s - v) v‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).1]
  exact (uncut_rawEndpoint_height hh hs0 hs1 hv.1.le).2

theorem uncut_circleEndpoint_intervalIntegrable {h s : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    IntervalIntegrable (fun v => circleKernel h 0 (s - v) v) volume 0 1 := by
  apply (uncut_rawEndpoint_intervalIntegrable hh hs0 hs1).congr_uIoo
  intro v hv
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
  exact (uncut_endpoint_no_wrap hh.le hh1 hs0 hs1 hv.1 hv.2).symm

theorem circleEndpoint_average_le_density {h α s : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs0 : 0 < s) (hs1 : s < 1) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤
        ScalarEndpointDensity.averagedDensity h s := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh0 hα).1
  · rw [← integral_uncut_circleEndpoint hh0 hh1 hs0 hs1]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (circleEndpoint_intervalIntegrable hh0 hα s)
      (uncut_circleEndpoint_intervalIntegrable hh0 hh1.le hs0 hs1)
    intro v _
    exact rawKernel_le_uncut hh0.le
      ⟨Int.fract_nonneg (s - v), (Int.fract_lt_one (s - v)).le⟩

theorem stronglyMeasurable_circleEndpoint_average (h α : ℝ) :
    StronglyMeasurable (fun s => ∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) := by
  have hm := (measurable_circleEndpoint_pair h α).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem circleEndpoint_average_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (h * α)⁻¹ := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro v _
    exact (rawKernel_height hh hα).1
  · calc
      _ ≤ ∫ _v in (0 : ℝ)..1, (h * α)⁻¹ :=
        intervalIntegral.integral_mono_on (by norm_num)
          (circleEndpoint_intervalIntegrable hh hα s) intervalIntegrable_const
          (fun _ _ => (rawKernel_height hh hα).2)
      _ = _ := by simp

theorem intervalIntegrable_square_of_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)))
    (hC : 0 ≤ C) (hb : ∀ s ∈ Ioo (0 : ℝ) 1, |f s| ≤ C) :
    IntervalIntegrable (fun s => (f s) ^ 2) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    (hf.pow 2) (C ^ 2)
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hne] with s hs hne
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hbound := hb s ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
  change ‖(f s) ^ 2‖ ≤ C ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using hbound)

theorem circleEndpoint_averaged_secondMoment {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) ≤
      1 + h^2 / (1 - h)^2 := by
  have hcut : IntervalIntegrable
      (fun s => (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (stronglyMeasurable_circleEndpoint_average h α).aestronglyMeasurable
      (show 0 ≤ (h * α)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (circleEndpoint_average_height hh0 hα s).1]
    exact (circleEndpoint_average_height hh0 hα s).2
  have huncut : IntervalIntegrable
      (fun s => (ScalarEndpointDensity.averagedDensity h s)^2) volume 0 1 := by
    apply intervalIntegrable_square_of_bound
      (ScalarEndpointDensity.averagedDensity_intervalIntegrable hh0 hh1).def'.aestronglyMeasurable
      (show 0 ≤ (1 - h)⁻¹ by positivity)
    intro s _
    rw [abs_of_nonneg (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)]
    exact ScalarEndpointDensity.averagedDensity_upper hh0 hh1 s
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, (ScalarEndpointDensity.averagedDensity h s)^2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hcut huncut
      intro s hs
      have hp := circleEndpoint_average_le_density hh0 hh1 hα hs.1 hs.2
      exact (sq_le_sq₀ hp.1 (ScalarEndpointDensity.averagedDensity_nonneg hh0 hh1 s)).mpr hp.2
    _ ≤ _ := ScalarEndpointDensity.averagedDensity_second_moment hh0 hh1

theorem manuscriptEndpointKernel_averaged_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hm1 (by norm_num)
  exact circleEndpoint_averaged_secondMoment hh hh1 hα

theorem circleEndpoint_periodize (h α s v : ℝ) :
    circleKernel h α (Int.fract s - v) v = circleKernel h α (s - v) v := by
  unfold circleKernel
  congr 1
  calc
    Int.fract (Int.fract s - v) = Int.fract ((s - v) - (⌊s⌋ : ℝ)) := by
      congr 1
      unfold Int.fract
      ring
    _ = _ := Int.fract_sub_intCast _ _

theorem circleEndpoint_at_zero {h α v : ℝ} (_hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hv0 : 0 < v) (hv1 : v < 1) : circleKernel h α (0 - v) v = 0 := by
  have hfract : Int.fract (-v) = 1 - v := by
    rw [Int.fract_neg (by rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]; exact hv0.ne'),
      Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold circleKernel
  rw [zero_sub, hfract, Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro hv
    have hd0 : 0 ≤ delta (1 - v) := delta_nonneg ⟨by linarith, by linarith⟩
    have hd : delta (1 - v) ≤ v := by
      unfold delta
      exact (min_le_right _ _).trans (by linarith)
    have hm : h * delta (1 - v) ≤ delta (1 - v) :=
      (mul_le_mul_of_nonneg_right hh1 hd0).trans_eq (one_mul _)
    linarith [hv.2]
  · rfl

theorem integral_circleEndpoint_at_zero {h α : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h α (0 - v) v) = 0 := by
  calc
    _ = ∫ _v in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact circleEndpoint_at_zero hh0 hh1 hv.1 hv.2
    _ = _ := by simp

theorem circleEndpoint_average_uniform_bound {h α : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1) (hα : 0 < α) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ∧
      (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) ≤ (1 - h)⁻¹ := by
  refine ⟨(circleEndpoint_average_height hh0 hα s).1, ?_⟩
  have heq : (∫ v in (0 : ℝ)..1, circleKernel h α (s - v) v) =
      ∫ v in (0 : ℝ)..1, circleKernel h α (Int.fract s - v) v := by
    apply intervalIntegral.integral_congr
    intro v _
    exact (circleEndpoint_periodize h α s v).symm
  rw [heq]
  by_cases hs : Int.fract s = 0
  · rw [hs, integral_circleEndpoint_at_zero hh0.le hh1.le]
    positivity
  · have hs0 : 0 < Int.fract s := lt_of_le_of_ne (Int.fract_nonneg s) (Ne.symm hs)
    exact (circleEndpoint_average_le_density hh0 hh1 hα hs0 (Int.fract_lt_one s)).2.trans
      (ScalarEndpointDensity.averagedDensity_upper hh0 hh1 _)

theorem manuscript_width_le_half {m : ℕ} (hm : 200 ≤ m) :
    (m : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 / 2 := by
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast (by omega : 4 ≤ m)
  calc
    _ ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hm4 (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
      norm_num

theorem manuscriptEndpointKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v) ≤ 2 := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hhalf := manuscript_width_le_half hm
  have hh1 : (m : ℝ)^(-(3 / 5 : ℝ)) < 1 := by linarith
  have hb := circleEndpoint_average_uniform_bound hh hh1 hα s
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 2 := by norm_num

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma antitone_variation_Icc_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (f a - f b) := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u i) - f (u (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_comm, edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u i) - f (u (i + 1)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg.mpr (hf (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (f (u 0) - f (u n)) := by
      congr 1
      exact Finset.sum_range_sub' (fun i => f (u i)) n
    _ ≤ ENNReal.ofReal (f a - f b) := by
      apply ENNReal.ofReal_le_ofReal
      have hab : a ≤ b := (hus 0).1.trans (hus 0).2
      exact sub_le_sub (hf ⟨le_rfl, hab⟩ (hus 0) (hus 0).1)
        (hf (hus n) ⟨hab, le_rfl⟩ (hus n).2)

theorem interval_indicator_variation_le {L C : ℝ}
    (hL : 0 < L) (hLone : L ≤ 1) (hC : 0 ≤ C) :
    eVariationOn ((Ioo 0 L).indicator (fun _ => C)) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * C) := by
  let f : ℝ → ℝ := (Ioo 0 L).indicator (fun _ => C)
  have hhalf : 0 < L / 2 := by linarith
  have hhalfL : L / 2 < L := by linarith
  have hhalfOne : L / 2 ≤ 1 := by linarith
  have hnonneg (x : ℝ) : 0 ≤ f x := Set.indicator_nonneg (fun _ _ => hC) x
  have hleft : MonotoneOn f (Icc 0 (L / 2)) := by
    intro x hx y hy hxy
    by_cases hx0 : 0 < x
    · have hy0 : 0 < y := hx0.trans_le hxy
      have hxL : x < L := hx.2.trans_lt hhalfL
      have hyL : y < L := hy.2.trans_lt hhalfL
      simp [f, hx0, hy0, hxL, hyL]
    · have hfx : f x = 0 := Set.indicator_of_notMem (by simp [hx0]) _
      rw [hfx]
      exact hnonneg y
  have hright : AntitoneOn f (Icc (L / 2) 1) := by
    intro x hx y hy hxy
    by_cases hyL : y < L
    · have hxL : x < L := hxy.trans_lt hyL
      have hx0 : 0 < x := hhalf.trans_le hx.1
      have hy0 : 0 < y := hhalf.trans_le hy.1
      simp [f, hx0, hy0, hxL, hyL]
    · have hfy : f y = 0 := Set.indicator_of_notMem (by simp [hyL]) _
      rw [hfy]
      exact hnonneg x
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 0 := by simp [f, not_lt.mpr hLone]
  have hfc : f (L / 2) = C := by simp [f, hhalf, hhalfL]
  have hleftBound : eVariationOn f (Icc 0 (L / 2)) ≤ ENNReal.ofReal C := by
    simpa only [inter_self, hf0, hfc, sub_zero] using
      (hleft.eVariationOn_eq ⟨le_rfl, hhalf.le⟩ ⟨hhalf.le, le_rfl⟩).le
  have hrightBound : eVariationOn f (Icc (L / 2) 1) ≤ ENNReal.ofReal C := by
    simpa only [hfc, hf1, sub_zero] using antitone_variation_Icc_le hright
  change eVariationOn f (Icc 0 1) ≤ ENNReal.ofReal (2 * C)
  calc
    eVariationOn f (Icc 0 1) =
        eVariationOn f (Icc 0 (L / 2)) + eVariationOn f (Icc (L / 2) 1) := by
      simpa only [univ_inter] using
        (eVariationOn.Icc_add_Icc f hhalf.le hhalfOne (mem_univ (L / 2))).symm
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add hleftBound hrightBound
    _ = ENNReal.ofReal (2 * C) := by rw [← ENNReal.ofReal_add hC hC]; congr 1; ring

theorem rawKernel_le_height {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    rawKernel h α s t ≤ (h * α)⁻¹ := by
  unfold rawKernel
  split_ifs with hs
  · by_cases ht : t ∈ Ioo 0 (h * delta s)
    · rw [Set.indicator_of_mem ht]
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    · rw [Set.indicator_of_notMem ht]
      positivity
  · positivity

theorem rawKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (rawKernel h α s) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  by_cases hs : α ≤ delta s
  · have hdelta : 0 < delta s := hα.trans_le hs
    have hL : 0 < h * delta s := mul_pos hh hdelta
    have hLone : h * delta s ≤ 1 := by
      calc
        h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone hdelta.le
        _ ≤ 1 := by nlinarith [delta_le_half s]
    have hi : (h * delta s)⁻¹ ≤ (h * α)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hs hh.le)
    have hfun : rawKernel h α s = (Ioo 0 (h * delta s)).indicator
        (fun _ => (h * delta s)⁻¹) := by
      funext t
      simp only [rawKernel, ite_eq_left hs]
    rw [hfun]
    exact (interval_indicator_variation_le hL hLone (inv_nonneg.mpr hL.le)).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hi (by norm_num)))
  · simp [rawKernel, hs, eVariationOn]

lemma rawKernel_zero (h α s : ℝ) : rawKernel h α s 0 = 0 := by
  unfold rawKernel
  split_ifs <;> simp

lemma rawKernel_one {h α s : ℝ} (hhone : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    rawKernel h α s 1 = 0 := by
  have hLone : h * delta s ≤ 1 := by
    calc
      h * delta s ≤ 1 * delta s := mul_le_mul_of_nonneg_right hhone (delta_nonneg hs)
      _ ≤ 1 := by nlinarith [delta_le_half s]
  unfold rawKernel
  split_ifs
  · apply Set.indicator_of_notMem
    intro ht
    exact (not_lt.mpr hLone) ht.2
  · rfl

lemma circleKernel_eq_raw_on_unit {h α : ℝ} (hhone : h ≤ 1) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α z v = rawKernel h α (Int.fract z) v := by
  rcases lt_or_eq_of_le hv.2 with hlt | heq
  · simp only [circleKernel, Int.fract_eq_self.mpr ⟨hv.1, hlt⟩]
  · subst v
    simp only [circleKernel, Int.fract_one, rawKernel_zero]
    exact (rawKernel_one hhone ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩).symm

theorem circleKernel_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (circleKernel h α z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (h * α)⁻¹) := by
  rw [eVariationOn.congr (fun _ hv => circleKernel_eq_raw_on_unit hhone z hv)]
  exact rawKernel_variation_le hh hhone hα (Int.fract z)

lemma manuscript_reciprocal_height {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ) ^ (-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ = (m : ℝ) ^ (13 / 5 : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have htwo : 1 / (m : ℝ)^2 = (m : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hmpos.le, Real.rpow_two]
    simp only [one_div]
  rw [htwo, ← Real.rpow_add hmpos, ← Real.rpow_neg hmpos.le]
  congr 1
  norm_num

theorem manuscriptKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (2 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (circleKernel _ _ z) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using circleKernel_variation_le hh hhone hα z

theorem manuscriptKernel_le_height {m : ℕ} (hm : 200 ≤ m) (z v : ℝ) :
    manuscriptKernel m z v ≤ (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, circleKernel, manuscript_reciprocal_height hm] using
    rawKernel_le_height hh hα (Int.fract z) (Int.fract v)

theorem manuscriptKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hnonneg : 0 ≤ manuscriptKernel m z v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
  dsimp only
  rw [abs_of_nonneg hnonneg]
  exact manuscriptKernel_le_height hm z v

theorem manuscriptKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
          (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        3 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptKernel_variation_le hm z)
    have hf := manuscriptKernel_sup_le hm z
    linarith

theorem manuscriptKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptKernel m z v|)) +
        (eVariationOn (manuscriptKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      3 * (m : ℝ)^10 := by
  calc
    _ ≤ 3 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptKernel_BV_bound hm z).2
    _ ≤ 3 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingShear
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma integrableOn_unitSquare_of_bound {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C) :
    IntegrableOn (Function.uncurry F) (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  exact IntegrableOn.of_bound hfinite hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => hC p.1 p.2))

theorem double_interval_integral_shear {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F)) (hC : ∀ x y, ‖F x y‖ ≤ C)
    (hperiodic : ∀ y, Function.Periodic (fun x => F x y) 1) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x - y) y) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y := by
  have hG : Measurable (fun p : ℝ × ℝ => F (p.1 - p.2) p.2) :=
    hF.comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hFi := integrableOn_unitSquare_of_bound hF hC
  have hGi := integrableOn_unitSquare_of_bound (F := fun x y => F (x - y) y) hG (fun x y => hC (x - y) y)
  rw [intervalIntegral_intervalIntegral_swap hGi, intervalIntegral_intervalIntegral_swap hFi]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  calc
    (∫ x in (0 : ℝ)..1, F (x - y) y) = ∫ x in (-y)..(-y + 1), F x y := by
      rw [intervalIntegral.integral_comp_sub_right (fun x => F x y) y]
      congr 1 <;> ring
    _ = ∫ x in (0 : ℝ)..1, F x y := by
      simpa only [zero_add] using (hperiodic y).intervalIntegral_add_eq (-y) 0

theorem measurable_circleKernel (h α : ℝ) :
    Measurable (Function.uncurry (circleKernel h α)) := by
  have hz : Measurable (fun p : ℝ × ℝ => Int.fract p.1) :=
    measurable_fract.comp measurable_fst
  have hv : Measurable (fun p : ℝ × ℝ => Int.fract p.2) :=
    measurable_fract.comp measurable_snd
  have hd : Measurable (fun p : ℝ × ℝ => delta (Int.fract p.1)) :=
    hz.min (measurable_const.sub hz)
  change Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2)
  simp only [circleKernel, rawKernel, Set.indicator_apply]
  apply Measurable.ite (measurableSet_le measurable_const hd)
  · apply Measurable.ite
    · exact (measurableSet_lt measurable_const hv).inter
        (measurableSet_lt hv (measurable_const.mul hd))
    · exact (measurable_const.mul hd).inv
    · exact measurable_const
  · exact measurable_const

lemma circleKernel_periodic_left (h α v : ℝ) :
    Function.Periodic (fun z => circleKernel h α z v) 1 := by
  intro z
  simp only [circleKernel, Int.fract_add_one]

lemma circleKernel_norm_le {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (z v : ℝ) :
    ‖circleKernel h α z v‖ ≤ (h * α)⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact rawKernel_le_height hh hα _ _
  · exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩

theorem endpoint_circleKernel_mass {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v) =
      1 - 2 * α := by
  rw [double_interval_integral_shear (measurable_circleKernel h α)
    (circleKernel_norm_le hh hα) (circleKernel_periodic_left h α)]
  exact double_interval_integral_circleKernel hh hhone hα hαhalf

theorem endpoint_circleKernel_secondMoment {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, circleKernel h α (z - v) v ^ 2) =
      (2 / h) * Real.log (1 / (2 * α)) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => circleKernel h α p.1 p.2 ^ 2) :=
    (measurable_circleKernel h α).pow_const 2
  have hbound (z v : ℝ) : ‖circleKernel h α z v ^ 2‖ ≤ ((h * α)⁻¹)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (circleKernel_norm_le hh hα z v) 2
  have hper (v : ℝ) : Function.Periodic (fun z => circleKernel h α z v ^ 2) 1 := by
    intro z
    exact congrArg (fun x : ℝ => x^2) (circleKernel_periodic_left h α v z)
  rw [double_interval_integral_shear (F := fun z v => circleKernel h α z v ^ 2) hmeas hbound hper]
  exact double_interval_integral_sq_circleKernel hh hhone hα hαhalf

theorem manuscriptEndpointKernel_mass {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    endpoint_circleKernel_mass hh hhone hα hαhalf

theorem manuscriptEndpointKernel_secondMoment {m : ℕ} (hm : 200 ≤ m) :
    (∫ z in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v ^ 2) =
      (2 / (m : ℝ) ^ (-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have heq : 1 / (2 * (1 / (m : ℝ)^2)) = (m : ℝ)^2 / 2 := by
    field_simp [hmR.ne']
  simpa only [manuscriptEndpointKernel, manuscriptKernel, heq] using
    endpoint_circleKernel_secondMoment hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingEndpointVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set

namespace Invariant233.ScalarSampling

lemma variation_add_le {f g : ℝ → ℝ} {s : Set ℝ} :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) + g (u (i+1))) (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n, (edist (f (u (i+1))) (f (u i)) +
          edist (g (u (i+1))) (g (u i))) := by
      exact Finset.sum_le_sum (fun i _ => edist_add_add_le _ _ _ _)
    _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

lemma variation_mul_le {f g : ℝ → ℝ} {s : Set ℝ} {F G : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ x ∈ s, |f x| ≤ F) (hg : ∀ x ∈ s, |g x| ≤ G) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal F * eVariationOn g s + ENNReal.ofReal G * eVariationOn f s := by
  have hp (x y : ℝ) (hx : x ∈ s) (hy : y ∈ s) :
      edist (f x * g x) (f y * g y) ≤
        ENNReal.ofReal F * edist (g x) (g y) +
        ENNReal.ofReal G * edist (f x) (f y) := by
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_mul hF, ← ENNReal.ofReal_mul hG,
      ← ENNReal.ofReal_add (mul_nonneg hF (abs_nonneg _)) (mul_nonneg hG (abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by ring_nf
      _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hf x hx) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hg y hy) (abs_nonneg _))
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1)) * g (u (i+1))) (f (u i) * g (u i))) ≤
        ∑ i ∈ Finset.range n, (ENNReal.ofReal F * edist (g (u (i+1))) (g (u i)) +
          ENNReal.ofReal G * edist (f (u (i+1))) (f (u i))) :=
      Finset.sum_le_sum (fun i _ => hp _ _ (hus _) (hus _))
    _ = ENNReal.ofReal F * (∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i))) +
        ENNReal.ofReal G * (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_right (eVariationOn.sum_le hu hus) _)
      (mul_le_mul_right (eVariationOn.sum_le hu hus) _)

lemma monotone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  have h := (hf.eVariationOn_eq (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)).le
  simp only [inter_self] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by linarith [(hbound 0 (by norm_num)).1,
    (hbound 1 (by norm_num)).2]))

lemma antitone_variation_le_height {f : ℝ → ℝ} {C : ℝ}
    (hf : AntitoneOn f (Icc (0 : ℝ) 1))
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ f x ∧ f x ≤ C) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal C := by
  exact (antitone_variation_Icc_le hf).trans (ENNReal.ofReal_le_ofReal
    (by linarith [(hbound 0 (by norm_num)).2, (hbound 1 (by norm_num)).1]))

lemma variation_step_le (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    eVariationOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) ≤ 1 := by
  have hb (x : ℝ) (_ : x ∈ Icc (0 : ℝ) 1) :
      0 ≤ (if P x then (1 : ℝ) else 0) ∧ (if P x then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  rcases hP with hP | hP
  · have hm : MonotoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hx : P x
      · simp [hx, hP x y hxy hx]
      · simp [hx]; split_ifs <;> norm_num
    simpa using monotone_variation_le_height hm hb
  · have hm : AntitoneOn (fun x => if P x then (1 : ℝ) else 0) (Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      by_cases hy : P y
      · simp [hy, hP x y hxy hy]
      · simp [hy]; split_ifs <;> norm_num
    simpa using antitone_variation_le_height hm hb

lemma VariationControl.mask {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (P : ℝ → Prop) [DecidablePred P]
    (hP : (∀ x y, x ≤ y → P x → P y) ∨ (∀ x y, x ≤ y → P y → P x)) :
    VariationControl (fun x => if P x then f x else 0) C (V + C) := by
  constructor
  · intro x; split_ifs; exact hf.nonneg x; exact le_rfl
  · intro x; split_ifs; exact hf.le_height x; exact hC
  · let g : ℝ → ℝ := fun x => if P x then 1 else 0
    have heq : (fun x => if P x then f x else 0) = fun x => f x * g x := by
      funext x; simp only [g]; split_ifs <;> simp
    rw [heq]
    have hb : ∀ x ∈ Icc (0 : ℝ) 1, |g x| ≤ 1 := by
      intro x _; simp only [g]; split_ifs <;> norm_num
    calc
      eVariationOn (fun x => f x * g x) (Icc (0 : ℝ) 1) ≤
          ENNReal.ofReal C * eVariationOn g (Icc (0 : ℝ) 1) +
          ENNReal.ofReal 1 * eVariationOn f (Icc (0 : ℝ) 1) :=
        variation_mul_le hC (by norm_num)
          (fun x _ => by rw [abs_of_nonneg (hf.nonneg x)]; exact hf.le_height x) hb
      _ ≤ ENNReal.ofReal C * 1 + ENNReal.ofReal 1 * ENNReal.ofReal V :=
        add_le_add (mul_le_mul_right (variation_step_le P hP) _) (mul_le_mul_right hf.variation _)
      _ = ENNReal.ofReal (V + C) := by
        simp only [ENNReal.ofReal_one, mul_one, one_mul]
        rw [← ENNReal.ofReal_add hC hV, add_comm]

lemma clipped_reciprocal_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) :
    VariationControl (fun x => (h * max α (g x))⁻¹) (h * α)⁻¹ (h * α)⁻¹ := by
  have hpos (x : ℝ) : 0 < h * max α (g x) := mul_pos hh (hα.trans_le (le_max_left _ _))
  have hn (x : ℝ) : 0 ≤ (h * max α (g x))⁻¹ := inv_nonneg.mpr (hpos x).le
  have hb (x : ℝ) : (h * max α (g x))⁻¹ ≤ (h * α)⁻¹ := by
    exact inv_anti₀ (mul_pos hh hα) (mul_le_mul_of_nonneg_left (le_max_left _ _) hh.le)
  refine ⟨hn, hb, ?_⟩
  rcases hg with hg | hg
  · apply antitone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos x) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩
  · apply monotone_variation_le_height
    · intro x _ y _ hxy
      exact inv_anti₀ (hpos y) (mul_le_mul_of_nonneg_left (max_le_max_left α (hg hxy)) hh.le)
    · exact fun x _ => ⟨hn x, hb x⟩

lemma leftEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (s : ℝ) :
    VariationControl (leftEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => s - v)
    (Or.inr (show Antitone (fun v : ℝ => s - v) from fun _ _ hxy => sub_le_sub_left hxy s))
  have h1 := hb.mask hC hC (fun v => s - v ≤ 1 / 2)
    (Or.inl (by intro x y hxy hx; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (s - v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rightEndpointPiece_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (rightEndpointPiece h α s) (h * α)⁻¹ (5 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := clipped_reciprocal_control hh hα (fun v => 1 - s + v)
    (Or.inl (show Monotone (fun v : ℝ => 1 - s + v) from by intro x y hxy; dsimp <;> linarith))
  have h1 := hb.mask hC hC (fun v => 1 / 2 < s - v)
    (Or.inr (by intro x y hxy hy; linarith))
  have h2 := h1.mask hC (by positivity) (fun v => α ≤ 1 - s + v)
    (Or.inl (by intro x y hxy hx; linarith))
  have h3 := h2.mask hC (by positivity) (fun v => v < h * (1 - s + v))
    (Or.inr (by intro x y hxy hy; nlinarith))
  have h4 := h3.mask hC (by positivity) (fun v => 0 < v)
    (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  convert h4 using 1
  · rfl
  · ring

lemma rawEndpoint_eq_pieces (h α s v : ℝ) :
    rawKernel h α (s - v) v = leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
  by_cases hm : s - v ≤ 1 / 2
  · have hd : delta (s - v) = s - v := by
      unfold delta; rw [min_eq_left (by linarith)]
    have hn : ¬ 1 / 2 < s - v := not_lt.mpr hm
    by_cases hc : α ≤ s - v
    · simp only [rawKernel, hd, ite_eq_left hc, max_eq_right hc,
        leftEndpointPiece, rightEndpointPiece, ite_eq_left hm, ite_eq_right hn,
        Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_left hm, ite_eq_right hn]
      split_ifs <;> simp_all
  · have hm' : 1 / 2 < s - v := lt_of_not_ge hm
    have hd : delta (s - v) = 1 - s + v := by
      unfold delta; rw [min_eq_right (by linarith)]; ring
    by_cases hc : α ≤ 1 - s + v
    · simp only [rawKernel, hd, ite_eq_left hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm', max_eq_right hc, Set.indicator_apply, mem_Ioo]
      split_ifs <;> simp_all
    · simp only [rawKernel, hd, ite_eq_right hc, leftEndpointPiece, rightEndpointPiece,
        ite_eq_right hm, ite_eq_left hm']
      split_ifs <;> simp_all

theorem rawEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    eVariationOn (fun v => rawKernel h α (s - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have hl := (leftEndpointPiece_control hh hα s).variation
  have hr := (rightEndpointPiece_control hh hhone hα s).variation
  have heq : (fun v => rawKernel h α (s - v) v) =
      fun v => leftEndpointPiece h α s v + rightEndpointPiece h α s v := by
    funext v; exact rawEndpoint_eq_pieces h α s v
  rw [heq]
  calc
    _ ≤ eVariationOn (leftEndpointPiece h α s) (Icc (0 : ℝ) 1) +
        eVariationOn (rightEndpointPiece h α s) (Icc (0 : ℝ) 1) := variation_add_le
    _ ≤ ENNReal.ofReal (5 * (h * α)⁻¹) + ENNReal.ofReal (5 * (h * α)⁻¹) := add_le_add hl hr
    _ = ENNReal.ofReal (10 * (h * α)⁻¹) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring

theorem endpoint_no_wrap_on_unit {h α s v : ℝ} (_hh : 0 ≤ h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    circleKernel h α (s - v) v = rawKernel h α (s - v) v := by
  rcases lt_or_eq_of_le hv.2 with hvone | hvone
  · unfold circleKernel
    rw [Int.fract_eq_self.mpr ⟨hv.1, hvone⟩]
    by_cases hvs : v ≤ s
    · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith [hs.2, hv.1]⟩]
    · have hsv : s < v := lt_of_not_ge hvs
      have hcut : ¬ α ≤ delta (s - v) := by
        have hd : delta (s - v) ≤ s - v := min_le_left _ _
        linarith
      have hfloor : ⌊s - v⌋ = -1 := by
        apply Int.floor_eq_iff.mpr
        norm_num
        constructor <;> linarith [hs.1]
      have hfract : Int.fract (s - v) = s - v + 1 := by
        rw [Int.fract, hfloor]; norm_num
      rw [hfract]
      unfold rawKernel
      rw [ite_eq_right hcut]
      split_ifs
      · apply Set.indicator_of_notMem
        intro hmem
        have hd0 : 0 ≤ delta (s - v + 1) := by
          apply delta_nonneg; constructor <;> linarith [hs.1]
        have hd : delta (s - v + 1) ≤ v - s := by
          exact (min_le_right _ _).trans (by linarith)
        have hm : h * delta (s - v + 1) ≤ delta (s - v + 1) := by
          nlinarith
        linarith [hmem.2, hs.1]
      · rfl
  · subst v
    have hcut : ¬ α ≤ delta (s - 1) := by
      have hd : delta (s - 1) ≤ s - 1 := min_le_left _ _
      linarith [hs.2]
    simp only [circleKernel, Int.fract_one]
    rw [rawKernel_zero]
    simp only [rawKernel, ite_eq_right hcut]

lemma circleEndpoint_fract (h α z v : ℝ) :
    circleKernel h α (z - v) v = circleKernel h α (Int.fract z - v) v := by
  have heq : Int.fract z - v = (z - v) - (⌊z⌋ : ℤ) := by
    rw [Int.fract]; ring
  simp only [circleKernel, heq, Int.fract_sub_intCast]

theorem circleEndpoint_variation_le {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (z : ℝ) :
    eVariationOn (fun v => circleKernel h α (z - v) v) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (h * α)⁻¹) := by
  have heq : EqOn (fun v => circleKernel h α (z - v) v)
      (fun v => rawKernel h α (Int.fract z - v) v) (Icc (0 : ℝ) 1) := by
    intro v hv
    dsimp only
    rw [circleEndpoint_fract]
    exact endpoint_no_wrap_on_unit hh.le hhone hα ⟨Int.fract_nonneg z, Int.fract_lt_one z⟩ hv
  rw [eVariationOn.congr heq]
  exact rawEndpoint_variation_le hh hhone hα _

theorem manuscriptEndpointKernel_variation_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (10 * (m : ℝ) ^ (13 / 5 : ℝ)) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  change eVariationOn (fun v => circleKernel _ _ (z - v) v) _ ≤ _
  simpa only [manuscript_reciprocal_height hm] using
    circleEndpoint_variation_le hh hhone hα z

theorem manuscriptEndpointKernel_sup_le {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) ≤
      (m : ℝ) ^ (13 / 5 : ℝ) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have hh := (manuscript_parameters hm).1
  have hn : 0 ≤ manuscriptKernel m (z-v) v :=
    rawKernel_nonneg hh.le ⟨Int.fract_nonneg (z-v), (Int.fract_lt_one (z-v)).le⟩
  dsimp only [manuscriptEndpointKernel]
  rw [abs_of_nonneg hn]
  exact manuscriptKernel_le_height hm _ _

theorem manuscriptEndpointKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    BoundedVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
          (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
        11 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (manuscriptEndpointKernel_variation_le hm z)
  · have hv := ENNReal.toReal_le_of_le_ofReal
      (by positivity) (manuscriptEndpointKernel_variation_le hm z)
    have hf := manuscriptEndpointKernel_sup_le hm z
    linarith

theorem manuscriptEndpointKernel_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) (z : ℝ) :
    sSup (Set.range (fun v : ℝ => |manuscriptEndpointKernel m z v|)) +
        (eVariationOn (manuscriptEndpointKernel m z) (Icc (0 : ℝ) 1)).toReal ≤
      11 * (m : ℝ)^10 := by
  calc
    _ ≤ 11 * (m : ℝ) ^ (13 / 5 : ℝ) := (manuscriptEndpointKernel_BV_bound hm z).2
    _ ≤ 11 * (m : ℝ)^10 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
        (by norm_num)

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingJensen
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma sq_integral_le_integral_sq_unit {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (hfsq : IntervalIntegrable (fun x => f x ^ 2) volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x)^2 ≤ ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  let c : ℝ := ∫ x in (0 : ℝ)..1, f x
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, (f x - c)^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  have heq : (fun x => (f x - c)^2) = fun x => (f x^2 - (2*c)*f x) + c^2 := by
    funext x; ring
  rw [heq, intervalIntegral.integral_add (hfsq.sub (hf.const_mul (2*c)))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c^2) volume 0 1),
    intervalIntegral.integral_sub hfsq (hf.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [sub_zero, one_smul] at hn
  change c^2 ≤ ∫ x in (0 : ℝ)..1, f x^2
  change 0 ≤ (∫ x in (0 : ℝ)..1, f x^2) - (2*c)*c + c^2 at hn
  nlinarith

lemma intervalIntegrable_unit_of_measurable_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply IntegrableOn.of_bound (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall hb

lemma measurable_interval_average {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫ y in (0 : ℝ)..1, F x y) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

lemma endpoint_average_integrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α) :
    IntervalIntegrable (fun z => ∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v) volume 0 1 ∧
    IntervalIntegrable (fun z => (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2) volume 0 1 := by
  have hm : Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1-p.2) p.2) :=
    (measurable_circleKernel h α).comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hbar := measurable_interval_average (F := fun z v => circleKernel h α (z-v) v) hm
  have hb (z : ℝ) : ‖∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v‖ ≤ (h*α)⁻¹ := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun v (_ : v ∈ uIoc (0 : ℝ) 1) => circleKernel_norm_le hh hα (z-v) v)
  constructor
  · exact intervalIntegrable_unit_of_measurable_bound hbar hb
  · apply intervalIntegrable_unit_of_measurable_bound (hbar.pow_const 2)
    intro z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2

theorem circleEndpoint_averaged_secondMoment_lower {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (1 - 2*α)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2 := by
  obtain ⟨hi, hisq⟩ := endpoint_average_integrable hh hα
  have hj := sq_integral_le_integral_sq_unit hi hisq
  rwa [endpoint_circleKernel_mass hh hhone hα hαhalf] at hj

theorem manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    circleEndpoint_averaged_secondMoment_lower hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarKernelEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem manuscriptKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ≤ 2 := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  have hb := averaged_circleKernel_bounds hh hhone hα s
  exact ⟨hb.1, hb.2.trans (by norm_num)⟩

theorem manuscriptKernel_averaged_secondMoment_exact {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    integral_sq_averaged_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_averaged_secondMoment_bounds {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤
      (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ∧
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  rw [manuscriptKernel_averaged_secondMoment_exact hm]
  have hα := (manuscript_parameters hm).2.2
  have hq0 : 0 ≤ 2 / (m : ℝ)^2 := by positivity
  have hq1 : 2 / (m : ℝ)^2 ≤ 1 := by
    have := hα.2
    rw [div_eq_mul_inv] at this ⊢
    nlinarith
  constructor
  · nlinarith
  · have : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith

theorem manuscriptKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptKernel m) where
  boundedVariation s := (manuscriptKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptKernel_BV_bound hm s).2.trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  variation_coarse s := (manuscriptKernel_BV_bound_ten hm s).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  average_bounds := manuscriptKernel_averaged_bounds hm
  mass := manuscriptKernel_mass hm
  average_square_lower := (manuscriptKernel_averaged_secondMoment_bounds hm).1
  average_square_upper := (manuscriptKernel_averaged_secondMoment_bounds hm).2
  square_mass := manuscriptKernel_secondMoment hm

theorem manuscriptEndpointKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptEndpointKernel m) where
  boundedVariation s := (manuscriptEndpointKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptEndpointKernel_BV_bound hm s).2
  variation_coarse := manuscriptEndpointKernel_BV_bound_ten hm
  average_bounds := manuscriptEndpointKernel_averaged_bounds hm
  mass := manuscriptEndpointKernel_mass hm
  average_square_lower := manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass hm
  average_square_upper := manuscriptEndpointKernel_averaged_secondMoment hm
  square_mass := manuscriptEndpointKernel_secondMoment hm

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_UniformIntervalPhase
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformIntervalPhase

theorem lambdaLaw_probability (N₀ : ℝ) (hN : 0 < N₀) :
    IsProbabilityMeasure (lambdaLaw N₀) := by
  constructor
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    Real.volume_Icc, heq, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hN.le]
  have heq' : N₀ * (1 / N₀) = 1 := by field_simp
  rw [heq', ENNReal.ofReal_one]

theorem lambdaLaw_eq_cond (N₀ : ℝ) (hN : 0 < N₀) :
    lambdaLaw N₀ = ProbabilityTheory.cond volume (Icc (1 / N₀) (2 / N₀)) := by
  have heq : 2 / N₀ - 1 / N₀ = 1 / N₀ := by ring
  simp only [lambdaLaw, ProbabilityTheory.cond, Real.volume_Icc]
  rw [heq, one_div, ENNReal.ofReal_inv_of_pos hN, inv_inv]

end Invariant233.UniformIntervalPhase

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarKernelMomentNumerics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem twice_kernel_square_mass_le {m : ℕ} (hm : 200 ≤ m) :
    2 * ((2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2)) ≤
      8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((m : ℝ)^2 / 2) ≤ 2 * Real.log (m : ℝ) := by
    calc
      _ ≤ Real.log ((m : ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (m : ℝ)])
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [Real.rpow_neg hm0.le, div_inv_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hlog (Real.rpow_pos_of_pos hm0 (3 / 5 : ℝ)).le]

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularEndpointKernel
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem endpoint_triangularKernel_eq_indicator {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (t : ℝ) :
    triangularKernel (Int.fract (s - t)) t = (Ioc 0 s).indicator (fun _ => 1) t := by
  have hsupport : t ∈ Ioo 0 (1 - Int.fract (s - t)) ↔ t ∈ Ioc 0 s := by
    constructor
    · intro ht
      refine ⟨ht.1, ?_⟩
      by_contra hts
      have hst : s < t := lt_of_not_ge hts
      have htone : t < 1 := by linarith [ht.2, Int.fract_nonneg (s - t)]
      have hfrac : Int.fract (s - t) = s - t + 1 := by
        rw [← Int.fract_add_one (s - t)]
        exact Int.fract_eq_self.mpr ⟨by linarith [hs.1], by linarith⟩
      rw [hfrac] at ht
      linarith [hs.1, ht.2]
    · intro ht
      have hfrac : Int.fract (s - t) = s - t :=
        Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht.2, by linarith [hs.2, ht.1]⟩
      rw [mem_Ioo, hfrac]
      exact ⟨ht.1, by linarith [hs.2]⟩
  simp only [triangularKernel, Set.indicator_apply, hsupport]

theorem interval_integral_endpoint_triangularKernel {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) = s := by
  simp_rw [endpoint_triangularKernel_eq_indicator hs]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator_const _ measurableSet_Ioc,
      Real.volume_real_Ioc_of_le hs.1]
    simp
  · intro t ht
    apply Set.indicator_of_notMem
    intro hts
    exact ht ⟨hts.1, hts.2.trans hs.2.le⟩

theorem endpoint_triangularKernel_fract (s t : ℝ) :
    triangularKernel (Int.fract (s - t)) t =
      triangularKernel (Int.fract (Int.fract s - t)) t := by
  have heq : Int.fract s - t = (s - t) - (⌊s⌋ : ℤ) := by
    rw [Int.fract]
    ring
  simp only [heq, Int.fract_sub_intCast]

theorem interval_integral_endpoint_triangularKernel_periodic (s : ℝ) :
    (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) = Int.fract s := by
  simp_rw [endpoint_triangularKernel_fract s]
  exact interval_integral_endpoint_triangularKernel
    ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩

theorem endpoint_triangularKernel_mass :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      triangularKernel (Int.fract (s - t)) t) = 1 / 2 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, s := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro s hs
      exact interval_integral_endpoint_triangularKernel ⟨hs.1.le, hs.2⟩
    _ = 1 / 2 := by norm_num

theorem endpoint_triangularKernel_secondMoment :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      triangularKernel (Int.fract (s - t)) t ^ 2) = 1 / 2 := by
  simp_rw [triangularKernel_sq]
  exact endpoint_triangularKernel_mass

theorem endpoint_triangularKernel_averaged_secondMoment :
    (∫ s in (0 : ℝ)..1,
      (∫ t in (0 : ℝ)..1, triangularKernel (Int.fract (s - t)) t) ^ 2) = 1 / 3 := by
  calc
    _ = ∫ s in (0 : ℝ)..1, s ^ 2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)
      intro s hs
      dsimp only
      rw [interval_integral_endpoint_triangularKernel ⟨hs.1.le, hs.2⟩]
    _ = 1 / 3 := by norm_num

private theorem lower_interval_control (s : ℝ) :
    VariationControl ((Ioc 0 s).indicator (fun _ => (1 : ℝ))) 1 2 := by
  have hstep : VariationControl (fun t : ℝ => if 0 < t then 1 else 0) 1 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t; split_ifs <;> norm_num
    · intro t; split_ifs <;> norm_num
    · simpa using variation_step_le (fun t : ℝ => 0 < t)
        (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  have hmask := hstep.mask (by norm_num) (by norm_num) (fun t => t ≤ s)
    (Or.inr (by intro x y hxy hy; exact hxy.trans hy))
  convert hmask using 1
  · funext t
    by_cases ht : 0 < t <;> by_cases hts : t ≤ s <;> simp [ht, hts]
  · norm_num

theorem triangularKernel_control (s : ℝ) : VariationControl (triangularKernel s) 1 2 := by
  have hstep : VariationControl (fun t : ℝ => if 0 < t then 1 else 0) 1 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t; split_ifs <;> norm_num
    · intro t; split_ifs <;> norm_num
    · simpa using variation_step_le (fun t : ℝ => 0 < t)
        (Or.inl (by intro x y hxy hx; exact hx.trans_le hxy))
  have hmask := hstep.mask (by norm_num) (by norm_num) (fun t => t < 1 - s)
    (Or.inr (by intro x y hxy hy; exact hxy.trans_lt hy))
  convert hmask using 1
  · funext t
    by_cases ht : 0 < t <;> by_cases hts : t < 1 - s <;>
      simp [triangularKernel, ht, hts]
  · norm_num

theorem endpoint_triangularKernel_control {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (fun t => triangularKernel (Int.fract (s - t)) t) 1 2 := by
  have heq : (fun t => triangularKernel (Int.fract (s - t)) t) =
      (Ioc 0 s).indicator (fun _ => (1 : ℝ)) := by
    funext t
    exact endpoint_triangularKernel_eq_indicator hs t
  rw [heq]
  exact lower_interval_control s

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TestedTriangularMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedTriangular

private theorem intervalIntegrable_of_unit_bound {f : ℝ → ℝ}
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    IntervalIntegrable f volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).2
  exact IntegrableOn.of_bound (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hbound)

private theorem interval_average_measurable {u : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u)) :
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hu.stronglyMeasurable.integral_prod_right.measurable

private theorem norm_le_one_of_bounds {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : ‖x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
  exact hx.2

theorem dominated_unitKernel_moments {u K : ℝ → ℝ → ℝ}
    (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKbound : ∀ s t, 0 ≤ K s t ∧ K s t ≤ 1)
    (hubound : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t) :
    (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t)) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, u s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t) ^ 2) ≤
      (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, K s t) ^ 2) ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, u s t ^ 2) ≤
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, K s t ^ 2) := by
  have hu01 (s t : ℝ) : 0 ≤ u s t ∧ u s t ≤ 1 :=
    ⟨(hubound s t).1, (hubound s t).2.trans (hKbound s t).2⟩
  have ui (s : ℝ) : IntervalIntegrable (u s) volume 0 1 :=
    intervalIntegrable_of_unit_bound
      (hu.comp (measurable_const.prodMk measurable_id))
      (fun t => norm_le_one_of_bounds (hu01 s t))
  have Ki (s : ℝ) : IntervalIntegrable (K s) volume 0 1 :=
    intervalIntegrable_of_unit_bound
      (hK.comp (measurable_const.prodMk measurable_id))
      (fun t => norm_le_one_of_bounds (hKbound s t))
  have means (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t) := by
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hubound s t).1)
    · exact intervalIntegral.integral_mono zero_le_one (ui s) (Ki s)
        (fun t => (hubound s t).2)
  have Kmean01 (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, K s t) ∧
      (∫ t in (0 : ℝ)..1, K s t) ≤ 1 := by
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hKbound s t).1)
    · calc
        _ ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono zero_le_one (Ki s) intervalIntegrable_const
            (fun t => (hKbound s t).2)
        _ = 1 := by norm_num
  have umean01 (s : ℝ) : 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ 1 :=
    ⟨(means s).1, (means s).2.trans (Kmean01 s).2⟩
  have sq01 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : 0 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 :=
    ⟨sq_nonneg x, pow_le_one₀ hx.1 hx.2⟩
  refine ⟨ui, interval_average_measurable hu, means, fun s => (umean01 s).2, ?_, ?_⟩
  · apply intervalIntegral.integral_mono zero_le_one
      (intervalIntegrable_of_unit_bound ((interval_average_measurable hu).pow_const 2)
        (fun s => norm_le_one_of_bounds (sq01 (umean01 s))))
      (intervalIntegrable_of_unit_bound ((interval_average_measurable hK).pow_const 2)
        (fun s => norm_le_one_of_bounds (sq01 (Kmean01 s))))
    intro s
    exact pow_le_pow_left₀ (means s).1 (means s).2 2
  · have usq (s : ℝ) : IntervalIntegrable (fun t => u s t ^ 2) volume 0 1 :=
      intervalIntegrable_of_unit_bound
        ((hu.comp (measurable_const.prodMk measurable_id)).pow_const 2)
        (fun t => norm_le_one_of_bounds (sq01 (hu01 s t)))
    have Ksq (s : ℝ) : IntervalIntegrable (fun t => K s t ^ 2) volume 0 1 :=
      intervalIntegrable_of_unit_bound
        ((hK.comp (measurable_const.prodMk measurable_id)).pow_const 2)
        (fun t => norm_le_one_of_bounds (sq01 (hKbound s t)))
    have inner01 (v : ℝ → ℝ → ℝ)
        (vi : ∀ s, IntervalIntegrable (fun t => v s t ^ 2) volume 0 1)
        (vb : ∀ s t, 0 ≤ v s t ∧ v s t ≤ 1) (s : ℝ) :
        0 ≤ (∫ t in (0 : ℝ)..1, v s t ^ 2) ∧
          (∫ t in (0 : ℝ)..1, v s t ^ 2) ≤ 1 := by
      constructor
      · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)
      · calc
          _ ≤ ∫ _t in (0 : ℝ)..1, (1 : ℝ) :=
            intervalIntegral.integral_mono zero_le_one (vi s) intervalIntegrable_const
              (fun t => (sq01 (vb s t)).2)
          _ = 1 := by norm_num
    apply intervalIntegral.integral_mono zero_le_one
      (intervalIntegrable_of_unit_bound (interval_average_measurable (hu.pow_const 2))
        (fun s => norm_le_one_of_bounds (inner01 u usq hu01 s)))
      (intervalIntegrable_of_unit_bound (interval_average_measurable (hK.pow_const 2))
        (fun s => norm_le_one_of_bounds (inner01 K Ksq hKbound s)))
    intro s
    exact intervalIntegral.integral_mono zero_le_one (usq s) (Ksq s)
      (fun t => pow_le_pow_left₀ (hubound s t).1 (hubound s t).2 2)

theorem triangularKernel_measurable : Measurable (Function.uncurry triangularKernel) := by
  change Measurable (fun p : ℝ × ℝ => triangularKernel p.1 p.2)
  simp only [triangularKernel, Set.indicator_apply, Set.mem_Ioo]
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)))
    measurable_const measurable_const

theorem triangularKernel_bounds (s t : ℝ) :
    0 ≤ triangularKernel s t ∧ triangularKernel s t ≤ 1 := by
  unfold triangularKernel
  by_cases h : t ∈ Ioo 0 (1 - s) <;> simp [h]

theorem firstKernel_measurable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (firstKernel E F)) := by
  exact (triangularKernel_measurable.mul
    ((measurable_const.indicator hE).comp measurable_fst)).mul
    ((measurable_const.indicator hF).comp
      (measurable_fract.comp (measurable_fst.add measurable_snd)))

theorem firstKernel_bounds (E F : Set ℝ) (s t : ℝ) :
    0 ≤ firstKernel E F s t ∧ firstKernel E F s t ≤ triangularKernel s t := by
  have h := triangularKernel_bounds s t
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, h.1]

theorem firstKernel_moment_bounds {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∀ s, IntervalIntegrable (firstKernel E F s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, firstKernel E F s t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1,
      0 ≤ (∫ t in (0 : ℝ)..1, firstKernel E F s t) ∧
        (∫ t in (0 : ℝ)..1, firstKernel E F s t) ≤ 1 - s) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, firstKernel E F s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, firstKernel E F s t) ^ 2) ≤ 1 / 3 ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, firstKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hm, havg, hone, havgsq, hsq⟩ := dominated_unitKernel_moments
    (firstKernel_measurable hE hF) triangularKernel_measurable
    triangularKernel_bounds (firstKernel_bounds E F)
  refine ⟨hi, hm, ?_, hone, ?_, ?_⟩
  · intro s hs
    exact ⟨(havg s).1, (havg s).2.trans_eq (interval_integral_triangularKernel hs)⟩
  · exact havgsq.trans_eq triangularKernel_averaged_secondMoment
  · exact hsq.trans_eq triangularKernel_secondMoment

theorem endpointKernel_measurable :
    Measurable (fun p : ℝ × ℝ => triangularKernel (Int.fract (p.1 - p.2)) p.2) :=
  triangularKernel_measurable.comp
    ((measurable_fract.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)

theorem secondKernel_measurable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (secondKernel E F)) := by
  exact (endpointKernel_measurable.mul
    ((measurable_const.indicator hE).comp
      (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
    ((measurable_const.indicator hF).comp measurable_fst)

theorem secondKernel_bounds (E F : Set ℝ) (s t : ℝ) :
    0 ≤ secondKernel E F s t ∧
      secondKernel E F s t ≤ triangularKernel (Int.fract (s - t)) t := by
  have h := triangularKernel_bounds (Int.fract (s - t)) t
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, h.1]

theorem secondKernel_moment_bounds {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∀ s, IntervalIntegrable (secondKernel E F s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, secondKernel E F s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, secondKernel E F s t) ∧
      (∫ t in (0 : ℝ)..1, secondKernel E F s t) ≤ Int.fract s) ∧
    (∀ s, (∫ t in (0 : ℝ)..1, secondKernel E F s t) ≤ 1) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, secondKernel E F s t) ^ 2) ≤ 1 / 3 ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, secondKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hm, havg, hone, havgsq, hsq⟩ := dominated_unitKernel_moments
    (K := fun s t => triangularKernel (Int.fract (s - t)) t)
    (secondKernel_measurable hE hF) endpointKernel_measurable
    (fun s t => triangularKernel_bounds (Int.fract (s - t)) t) (secondKernel_bounds E F)
  refine ⟨hi, hm, ?_, hone, ?_, ?_⟩
  · intro s
    exact ⟨(havg s).1,
      (havg s).2.trans_eq (interval_integral_endpoint_triangularKernel_periodic s)⟩
  · exact havgsq.trans_eq endpoint_triangularKernel_averaged_secondMoment
  · exact hsq.trans_eq endpoint_triangularKernel_secondMoment

theorem firstKernel_sq (E F : Set ℝ) (s t : ℝ) :
    firstKernel E F s t ^ 2 = firstKernel E F s t := by
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, triangularKernel_sq]

theorem secondKernel_sq (E F : Set ℝ) (s t : ℝ) :
    secondKernel E F s t ^ 2 = secondKernel E F s t := by
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, triangularKernel_sq]

theorem testedKernel_square_integrable {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IntegrableOn (fun p : ℝ × ℝ => firstKernel E F p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) ∧
      IntegrableOn (fun p : ℝ × ℝ => secondKernel E F p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
  constructor
  · apply integrableOn_unitSquare_of_bound
      (F := fun s t => firstKernel E F s t ^ 2) (C := 1)
      ((firstKernel_measurable hE hF).pow_const 2)
    intro s t
    rw [firstKernel_sq, Real.norm_eq_abs, abs_of_nonneg (firstKernel_bounds E F s t).1]
    exact (firstKernel_bounds E F s t).2.trans (triangularKernel_bounds s t).2
  · apply integrableOn_unitSquare_of_bound
      (F := fun s t => secondKernel E F s t ^ 2) (C := 1)
      ((secondKernel_measurable hE hF).pow_const 2)
    intro s t
    rw [secondKernel_sq, Real.norm_eq_abs, abs_of_nonneg (secondKernel_bounds E F s t).1]
    exact (secondKernel_bounds E F s t).2.trans
      (triangularKernel_bounds (Int.fract (s - t)) t).2

theorem testedKernel_reverse_square_moments_le {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, firstKernel E F s t ^ 2) ≤ 1 / 2 ∧
    (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, secondKernel E F s t ^ 2) ≤ 1 / 2 := by
  obtain ⟨hi, hj⟩ := testedKernel_square_integrable hE hF
  constructor
  · rw [← intervalIntegral_intervalIntegral_swap
      (F := fun s t => firstKernel E F s t ^ 2) hi]
    exact (firstKernel_moment_bounds hE hF).2.2.2.2.2
  · rw [← intervalIntegral_intervalIntegral_swap
      (F := fun s t => secondKernel E F s t ^ 2) hj]
    exact (secondKernel_moment_bounds hE hF).2.2.2.2.2

end Invariant233.ScalarSampling.TestedTriangular

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TestedSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedSampling

theorem dominated_boundedKernel_moments {u K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKb : ∀ s t, 0 ≤ K s t ∧ K s t ≤ C)
    (hub : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t) :
    (∀ s, IntervalIntegrable (u s) volume 0 1) ∧
    Measurable (fun s => ∫ t in (0 : ℝ)..1, u s t) ∧
    (∀ s, 0 ≤ (∫ t in (0 : ℝ)..1, u s t) ∧
      (∫ t in (0 : ℝ)..1, u s t) ≤ (∫ t in (0 : ℝ)..1, K s t)) ∧
    (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, u s t) ^ 2) ≤
      (∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1, K s t) ^ 2) ∧
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, u s t ^ 2) ≤
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, K s t ^ 2) := by
  have hbK (s t : ℝ) : 0 ≤ K s t / C ∧ K s t / C ≤ 1 :=
    ⟨div_nonneg (hKb s t).1 hC.le, (div_le_one hC).2 (hKb s t).2⟩
  have hbu (s t : ℝ) : 0 ≤ u s t / C ∧ u s t / C ≤ K s t / C :=
    ⟨div_nonneg (hub s t).1 hC.le, div_le_div_of_nonneg_right (hub s t).2 hC.le⟩
  obtain ⟨hi, _, hm, _, ha, hb⟩ := TestedTriangular.dominated_unitKernel_moments
    (u := fun s t => u s t / C) (K := fun s t => K s t / C)
    (hu.div_const C) (hK.div_const C) hbK hbu
  refine ⟨?_, measurable_interval_average hu, ?_, ?_, ?_⟩
  · intro s
    convert (hi s).mul_const C using 1 <;> first | (with_reducible_and_instances rfl) | (simp [hC.ne'])
  · intro s
    have hs := hm s
    simp only [intervalIntegral.integral_div] at hs
    exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun t => (hub s t).1),
      (div_le_div_iff_of_pos_right hC).1 hs.2⟩
  · simp only [intervalIntegral.integral_div, div_pow] at ha
    exact (div_le_div_iff_of_pos_right (pow_pos hC 2)).1 ha
  · simp only [div_pow, intervalIntegral.integral_div] at hb
    exact (div_le_div_iff_of_pos_right (pow_pos hC 2)).1 hb

private theorem first_measurable (m : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (firstKernel m E F)) :=
  ((measurable_circleKernel _ _).mul
    ((measurable_const.indicator hE).comp measurable_fst)).mul
    ((measurable_const.indicator hF).comp
      (measurable_fract.comp (measurable_fst.add measurable_snd)))

private theorem second_measurable (m : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (Function.uncurry (secondKernel m E F)) :=
  ((measurable_circleEndpoint_pair _ _).mul
    ((measurable_const.indicator hE).comp
      (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
    ((measurable_const.indicator hF).comp measurable_fst)

private theorem momentBounds_of_domination {m : ℕ} {u K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hu : Measurable (Function.uncurry u))
    (hK : Measurable (Function.uncurry K))
    (hKb : ∀ s t, 0 ≤ K s t ∧ K s t ≤ C)
    (hub : ∀ s t, 0 ≤ u s t ∧ u s t ≤ K s t)
    (hest : KernelEstimates m K) : MomentBounds m u := by
  obtain ⟨hi, hm, hmean, havg, hsq⟩ := dominated_boundedKernel_moments hC hu hK hKb hub
  refine ⟨hi, hm, ?_, ?_, ?_⟩
  · intro s
    exact ⟨(hmean s).1, (hmean s).2.trans (hest.average_bounds s).2⟩
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _),
      havg.trans hest.average_square_upper⟩
  · have hsquare : IntegrableOn (fun p : ℝ × ℝ => u p.1 p.2 ^ 2)
        (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
      apply integrableOn_unitSquare_of_bound (F := fun s t => u s t ^ 2)
        (C := C ^ 2) (hu.pow_const 2)
      intro s t
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (hub s t).1]
      exact pow_le_pow_left₀ (hub s t).1 ((hub s t).2.trans (hKb s t).2) 2
    constructor
    · apply intervalIntegral.integral_nonneg_of_forall zero_le_one
      intro t
      exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)
    · rw [← intervalIntegral_intervalIntegral_swap (F := fun s t => u s t ^ 2) hsquare]
      exact hsq.trans_eq hest.square_mass

theorem firstKernel_moment_bounds {m : ℕ} (hm : 200 ≤ m) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (firstKernel m E F) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hb (s t : ℝ) : 0 ≤ manuscriptKernel m s t ∧
      manuscriptKernel m s t ≤
        ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ :=
    rawKernel_height hh hα
  apply momentBounds_of_domination (K := manuscriptKernel m)
    (inv_pos.mpr (mul_pos hh hα))
    (first_measurable m hE hF) (measurable_circleKernel _ _) hb
    (hest := manuscriptKernel_estimates hm)
  intro s t
  by_cases hs : s ∈ E <;> by_cases ht : Int.fract (s + t) ∈ F <;>
    simp [firstKernel, hs, ht, (hb s t).1]

theorem secondKernel_moment_bounds {m : ℕ} (hm : 200 ≤ m) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (secondKernel m E F) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hb (s t : ℝ) : 0 ≤ manuscriptEndpointKernel m s t ∧
      manuscriptEndpointKernel m s t ≤
        ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹ :=
    rawKernel_height hh hα
  apply momentBounds_of_domination (K := manuscriptEndpointKernel m)
    (inv_pos.mpr (mul_pos hh hα))
    (second_measurable m hE hF) (measurable_circleEndpoint_pair _ _) hb
    (hest := manuscriptEndpointKernel_estimates hm)
  intro s t
  by_cases hx : Int.fract (s - t) ∈ E <;> by_cases hy : s ∈ F <;>
    simp [secondKernel, hx, hy, (hb s t).1]

end Invariant233.ScalarSampling.TestedSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TestedKernelUnifiedMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedSampling

theorem half_le_common_square_bound {m : ℕ} (hm : 200 ≤ m) :
    (1 / 2 : ℝ) ≤ (2 / (m : ℝ)^(-(3 / 5 : ℝ))) *
      Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hh1, _, _⟩ := manuscript_parameters hm
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ)^2 / 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hfactor : (1 : ℝ) ≤ 2 / (m : ℝ)^(-(3 / 5 : ℝ)) :=
    (le_div_iff₀ hh).2 (by linarith)
  calc
    (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
    _ ≤ (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) :=
      mul_le_mul hfactor hlog (by norm_num) (by positivity)

theorem firstTriangular_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (TestedTriangular.firstKernel E F) := by
  obtain ⟨hi, hmeas, _, hmean, havg, _⟩ :=
    TestedTriangular.firstKernel_moment_bounds hE hF
  refine ⟨hi, hmeas, ?_, ?_, ?_⟩
  · intro s
    exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun t => (TestedTriangular.firstKernel_bounds E F s t).1),
      (hmean s).trans (by norm_num)⟩
  · refine ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun _ => sq_nonneg _), havg.trans ?_⟩
    have hnonneg : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)),
      (TestedTriangular.testedKernel_reverse_square_moments_le hE hF).1.trans
        (half_le_common_square_bound hm)⟩

theorem secondTriangular_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (TestedTriangular.secondKernel E F) := by
  obtain ⟨hi, hmeas, hnonneg, hmean, havg, _⟩ :=
    TestedTriangular.secondKernel_moment_bounds hE hF
  refine ⟨hi, hmeas, ?_, ?_, ?_⟩
  · intro s
    exact ⟨(hnonneg s).1, (hmean s).trans (by norm_num)⟩
  · refine ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun _ => sq_nonneg _), havg.trans ?_⟩
    have hnonneg : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)),
      (TestedTriangular.testedKernel_reverse_square_moments_le hE hF).2.trans
        (half_le_common_square_bound hm)⟩

end Invariant233.ScalarSampling.TestedSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TestedTriangularVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
attribute [local instance] Classical.propDecidable

namespace Invariant233.ScalarSampling.TestedTriangular

theorem firstKernel_interval_eq (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    firstKernel E (Ico a b) s t =
      if s ∈ E then
        if a ≤ s + t then if s + t < b then triangularKernel s t else 0 else 0
      else 0 := by
  by_cases ht : t ∈ Ioo 0 (1 - s)
  · have hfract : Int.fract (s + t) = s + t :=
      Int.fract_eq_self.mpr ⟨by linarith [hs.1, ht.1], by linarith [ht.2]⟩
    by_cases hE : s ∈ E <;> by_cases ha : a ≤ s + t <;> by_cases hb : s + t < b <;>
      simp [firstKernel, triangularKernel, ht, hfract, hE, ha, hb]
  · simp [firstKernel, triangularKernel, ht]

theorem secondKernel_interval_eq (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    secondKernel (Ico a b) F s t =
      if s ∈ F then
        if a ≤ s - t then
          if s - t < b then triangularKernel (Int.fract (s - t)) t else 0
        else 0
      else 0 := by
  by_cases ht : t ∈ Ioc 0 s
  · have hfract : Int.fract (s - t) = s - t :=
      Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht.2, by linarith [hs.2, ht.1]⟩
    by_cases hF : s ∈ F <;> by_cases ha : a ≤ s - t <;> by_cases hb : s - t < b <;>
      simp [secondKernel, hfract, hF, ha, hb]
  · have hzero : triangularKernel (Int.fract (s - t)) t = 0 := by
      rw [endpoint_triangularKernel_eq_indicator hs t]
      exact indicator_of_notMem ht _
    simp [secondKernel, hzero]

private theorem zero_control : VariationControl (fun _ : ℝ => 0) 1 4 := by
  refine ⟨fun _ => le_rfl, fun _ => zero_le_one, ?_⟩
  have hz := monotone_variation_le_height
    (f := fun _ : ℝ => 0) (C := 0) (by intro x hx y hy hxy; rfl)
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  exact hz.trans (by norm_num)

theorem firstKernel_interval_control (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (firstKernel E (Ico a b) s) 1 4 := by
  have h1 := (triangularKernel_control s).mask (by norm_num) (by norm_num)
    (fun t => s + t < b)
    (Or.inr (by intro x y hxy hy; linarith))
  have h2 := h1.mask (by norm_num) (by norm_num) (fun t => a ≤ s + t)
    (Or.inl (by intro x y hxy hx; linarith))
  by_cases hE : s ∈ E
  · convert h2 using 1
    · funext t
      simp only [firstKernel_interval_eq E a b hs t, ite_eq_left hE]
    · norm_num
  · have heq : firstKernel E (Ico a b) s = fun _ => 0 := by
      funext t
      simp [firstKernel_interval_eq E a b hs t, hE]
    rw [heq]
    exact zero_control

theorem secondKernel_interval_control (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    VariationControl (secondKernel (Ico a b) F s) 1 4 := by
  have h1 := (endpoint_triangularKernel_control hs).mask (by norm_num) (by norm_num)
    (fun t => s - t < b)
    (Or.inl (by intro x y hxy hx; linarith))
  have h2 := h1.mask (by norm_num) (by norm_num) (fun t => a ≤ s - t)
    (Or.inr (by intro x y hxy hy; linarith))
  by_cases hF : s ∈ F
  · convert h2 using 1
    · funext t
      simp only [secondKernel_interval_eq F a b hs t, ite_eq_left hF]
    · norm_num
  · have heq : secondKernel (Ico a b) F s = fun _ => 0 := by
      funext t
      simp [secondKernel_interval_eq F a b hs t, hF]
    rw [heq]
    exact zero_control

private theorem BV_bound_of_control {f : ℝ → ℝ} (hf : VariationControl f 1 4) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ 5 := by
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf.variation, ?_⟩
  have hv := ENNReal.toReal_le_of_le_ofReal (by norm_num) hf.variation
  have hh : sSup (Set.range (fun t => |f t|)) ≤ (1 : ℝ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    dsimp only
    rw [abs_of_nonneg (hf.nonneg t)]
    exact hf.le_height t
  linarith

theorem firstKernel_interval_BV_bound (E : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (firstKernel E (Ico a b) s) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |firstKernel E (Ico a b) s t|)) +
        (eVariationOn (firstKernel E (Ico a b) s) (Icc (0 : ℝ) 1)).toReal ≤ 5 :=
  BV_bound_of_control (firstKernel_interval_control E a b hs)

theorem secondKernel_interval_BV_bound (F : Set ℝ) (a b : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (secondKernel (Ico a b) F s) (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |secondKernel (Ico a b) F s t|)) +
        (eVariationOn (secondKernel (Ico a b) F s) (Icc (0 : ℝ) 1)).toReal ≤ 5 :=
  BV_bound_of_control (secondKernel_interval_control F a b hs)

end Invariant233.ScalarSampling.TestedTriangular

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularTestedVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace Invariant233.ScalarSampling

theorem VariationControl.mul_interval_indicator {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (g : ℝ → ℝ) (hg : Monotone g ∨ Antitone g) (a b : ℝ) :
    VariationControl (fun t => f t * (Ico a b).indicator (fun _ => 1) (g t))
      C (V + 2 * C) := by
  have ha : (∀ x y, x ≤ y → a ≤ g x → a ≤ g y) ∨
      (∀ x y, x ≤ y → a ≤ g y → a ≤ g x) := by
    rcases hg with hg | hg
    · exact Or.inl (fun _ _ hxy hx => hx.trans (hg hxy))
    · exact Or.inr (fun _ _ hxy hy => hy.trans (hg hxy))
  have hb : (∀ x y, x ≤ y → g x < b → g y < b) ∨
      (∀ x y, x ≤ y → g y < b → g x < b) := by
    rcases hg with hg | hg
    · exact Or.inr (fun _ _ hxy hy => (hg hxy).trans_lt hy)
    · exact Or.inl (fun _ _ hxy hx => (hg hxy).trans_lt hx)
  have h1 := hf.mask hC hV (fun t => a ≤ g t) ha
  have h2 := h1.mask hC (add_nonneg hV hC) (fun t => g t < b) hb
  convert h2 using 1
  · funext t
    by_cases hat : a ≤ g t <;> by_cases hbt : g t < b <;> simp [hat, hbt]
  · ring

theorem VariationControl.fixed_indicator_mul {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hC : 0 ≤ C) (E : Set ℝ) (s : ℝ) :
    VariationControl (fun t => E.indicator (fun _ => 1) s * f t) C V := by
  by_cases hs : s ∈ E
  · simpa [hs] using hf
  · simp only [Set.indicator_of_notMem hs, zero_mul]
    refine ⟨fun _ => le_rfl, fun _ => hC, ?_⟩
    have hzero : eVariationOn (fun _ : ℝ => (0 : ℝ)) (Icc (0 : ℝ) 1) = 0 := by
      apply (eVariationOn.eq_zero_iff _).2
      intro x hx y hy
      exact edist_self _
    rw [hzero]
    exact bot_le

theorem VariationControl.boundedVariation_sup_add_le {f : ℝ → ℝ} {C V : ℝ}
    (hf : VariationControl f C V) (hV : 0 ≤ V) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ C + V := by
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf.variation
  · have hv := ENNReal.toReal_le_of_le_ofReal hV hf.variation
    have hh : sSup (Set.range (fun t => |f t|)) ≤ C := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨t, rfl⟩
      dsimp only
      rw [abs_of_nonneg (hf.nonneg t)]
      exact hf.le_height t
    exact add_le_add hh hv

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem real_K_pos (n : ℕ) : 0 < (p.K n : ℝ) := by exact_mod_cast hp.K_pos n

theorem prefix_count_succ_le (n : ℕ) :
    (p.prefixCount (n + 1) : ℝ) ≤ (101 / 100 : ℝ) * p.m n := by
  have h := hp.prefix_count_le n
  simp only [ProductScaleData.prefixCount, Finset.sum_range_succ, Nat.cast_add] at *
  linarith

theorem K_strictMono : StrictMono p.K := by
  apply strictMono_nat_of_lt_succ
  intro n
  have := hp.K_double n
  omega

theorem m_lt_next_K (n : ℕ) : p.m n < p.K (n + 1) := by
  have hm : (20 : ℝ) ≤ p.m n := by exact_mod_cast le_trans (by decide) (hp.m_ge_100 n)
  have h := SamplingHorizon.twice_lt_ceiling_cutoff hm
  rw [← hp.next_K n] at h
  have hmpos : (0 : ℝ) < p.m n := by exact_mod_cast hp.m_pos n
  have : (p.m n : ℝ) < p.K (n + 1) := by linarith
  exact_mod_cast this

theorem m_strictMono : StrictMono p.m := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (hp.m_lt_next_K n).trans_le (hp.m_ge_K (n + 1))

theorem N_strictMono : StrictMono p.N := by
  intro n k hnk
  have hm : (p.m n : ℝ) < p.m k := by exact_mod_cast hp.m_strictMono hnk
  have hK : (p.K n : ℝ) < p.K k := by exact_mod_cast hp.K_strictMono hnk
  exact mul_lt_mul hm hK.le (hp.real_K_pos n) (by positivity)

theorem m_ge_pow_self (n : ℕ) : 2 ^ n ≤ p.m n := by
  have h := hp.m_ge_pow n
  have hpow : 2 ^ n ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  exact hpow.trans h

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingMomentBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

open MeasureTheory

theorem l2_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

end InvariantRotation.SamplingMomentBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingPhaseMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSamplingPhaseMoments

theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ t, f t ∂unitInterval) = ∫ t in (0 : ℝ)..1, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [unitInterval, restrict_Ico_eq_restrict_Ioc]

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingTestVariation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace Invariant233.ScalarSampling

lemma circleKernel_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (circleKernel h α s) (h * α)⁻¹ (2 * (h * α)⁻¹) := by
  refine ⟨?_, ?_, circleKernel_variation_le hh hhone hα s⟩
  · intro t
    exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  · intro t
    exact rawKernel_le_height hh hα _ _

lemma circleEndpoint_control {h α : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (s : ℝ) :
    VariationControl (fun t => circleKernel h α (s-t) t)
      (h * α)⁻¹ (10 * (h * α)⁻¹) := by
  refine ⟨?_, ?_, circleEndpoint_variation_le hh hhone hα s⟩
  · intro t
    exact rawKernel_nonneg hh.le ⟨Int.fract_nonneg (s-t), (Int.fract_lt_one (s-t)).le⟩
  · intro t
    exact rawKernel_le_height hh hα _ _

lemma rawKernel_support_of_ne_zero {h α s t : ℝ}
    (hk : rawKernel h α s t ≠ 0) :
    α ≤ delta s ∧ 0 < t ∧ t < h * delta s := by
  by_cases hc : α ≤ delta s
  · refine ⟨hc, ?_⟩
    by_contra ht
    apply hk
    simp only [rawKernel, ite_eq_left hc]
    exact Set.indicator_of_notMem (s := Ioo 0 (h * delta s)) (a := t) ht
      (fun _ : ℝ => (h * delta s)⁻¹)
  · exact False.elim (hk (by simp [rawKernel, hc]))

lemma circleKernel_target_no_wrap {h α s t : ℝ} (hhone : h ≤ 1)
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : circleKernel h α s t ≠ 0) : Int.fract (s+t) = s+t := by
  have hr : rawKernel h α s t ≠ 0 := by
    simpa only [circleKernel_eq_raw_on_unit hhone s ht,
      Int.fract_eq_self.mpr hs] using hk
  have hp := rawKernel_support_of_ne_zero hr
  have hd : 0 ≤ delta s := delta_nonneg ⟨hs.1, hs.2.le⟩
  have hwidth : h * delta s ≤ 1-s := by
    calc
      h * delta s ≤ delta s := by nlinarith
      _ ≤ 1-s := min_le_right _ _
  exact Int.fract_eq_self.mpr ⟨by linarith [ht.1, hs.1], by linarith [hp.2.2]⟩

lemma circleEndpoint_source_no_wrap {h α s t : ℝ} (hh : 0 ≤ h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : circleKernel h α (s-t) t ≠ 0) : Int.fract (s-t) = s-t := by
  have hr : rawKernel h α (s-t) t ≠ 0 := by
    rwa [endpoint_no_wrap_on_unit hh hhone hα hs ht] at hk
  have hp := (rawKernel_support_of_ne_zero hr).1
  have hleft : delta (s-t) ≤ s-t := min_le_left _ _
  have hright : delta (s-t) ≤ 1-(s-t) := min_le_right _ _
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

private lemma mul_two_tests_bounds {x C : ℝ} (hx : 0 ≤ x) (hxC : x ≤ C)
    (hC : 0 ≤ C) (E F : Set ℝ) (s t : ℝ) :
    0 ≤ x * E.indicator (fun _ => 1) s * F.indicator (fun _ => 1) t ∧
      x * E.indicator (fun _ => 1) s * F.indicator (fun _ => 1) t ≤ C := by
  by_cases hs : s ∈ E <;> by_cases ht : t ∈ F <;> simp [hs, ht, hx, hxC, hC]

theorem tested_circleKernel_control {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    VariationControl (fun t => circleKernel h α s t *
      (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)))
      (h * α)⁻¹ (4 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := circleKernel_control hh hhone hα s
  have hc := hb.mul_interval_indicator hC (by positivity) (fun t => s+t)
    (Or.inl (by intro x y hxy; dsimp only <;> linarith)) c d
  have hfixed : VariationControl (fun t => (Ico a b).indicator (fun _ => 1) s *
      (circleKernel h α s t * (Ico c d).indicator (fun _ => 1) (s+t)))
      (h * α)⁻¹ (4 * (h * α)⁻¹) := by
    convert hc.fixed_indicator_mul hC (Ico a b) s using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) s (Int.fract (s+t))).1
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) s (Int.fract (s+t))).2
  · have heq : EqOn (fun t => circleKernel h α s t *
        (Ico a b).indicator (fun _ => 1) s *
        (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)))
        (fun t => (Ico a b).indicator (fun _ => 1) s *
          (circleKernel h α s t * (Ico c d).indicator (fun _ => 1) (s+t)))
        (Icc (0 : ℝ) 1) := by
      intro t ht
      dsimp only
      by_cases hk : circleKernel h α s t = 0
      · simp [hk]
      · rw [circleKernel_target_no_wrap hhone hs ht hk]
        ring
    rw [eVariationOn.congr heq]
    exact hfixed.variation

theorem tested_circleEndpoint_control {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    VariationControl (fun t => circleKernel h α (s-t) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
      (Ico c d).indicator (fun _ => 1) s)
      (h * α)⁻¹ (12 * (h * α)⁻¹) := by
  have hC : 0 ≤ (h * α)⁻¹ := by positivity
  have hb := circleEndpoint_control hh hhone hα s
  have hc := hb.mul_interval_indicator hC (by positivity) (fun t => s-t)
    (Or.inr (by intro x y hxy; exact sub_le_sub_left hxy s)) a b
  have hfixed : VariationControl (fun t => (Ico c d).indicator (fun _ => 1) s *
      (circleKernel h α (s-t) t * (Ico a b).indicator (fun _ => 1) (s-t)))
      (h * α)⁻¹ (12 * (h * α)⁻¹) := by
    convert hc.fixed_indicator_mul hC (Ico c d) s using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) (Int.fract (s-t)) s).1
  · intro t
    exact (mul_two_tests_bounds (hb.nonneg t) (hb.le_height t) hC
      (Ico a b) (Ico c d) (Int.fract (s-t)) s).2
  · have heq : EqOn (fun t => circleKernel h α (s-t) t *
        (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
        (Ico c d).indicator (fun _ => 1) s)
        (fun t => (Ico c d).indicator (fun _ => 1) s *
          (circleKernel h α (s-t) t * (Ico a b).indicator (fun _ => 1) (s-t)))
        (Icc (0 : ℝ) 1) := by
      intro t ht
      dsimp only
      by_cases hk : circleKernel h α (s-t) t = 0
      · simp [hk]
      · rw [circleEndpoint_source_no_wrap hh.le hhone hα hs ht hk]
        ring
    rw [eVariationOn.congr heq]
    exact hfixed.variation

theorem tested_circleKernel_BV_bound {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => circleKernel h α s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        5 * (h * α)⁻¹ := by
  simpa only [show (h * α)⁻¹ + 4 * (h * α)⁻¹ = 5 * (h * α)⁻¹ by ring] using
    (tested_circleKernel_control hh hhone hα hs a b c d).boundedVariation_sup_add_le
      (by positivity)

theorem tested_circleEndpoint_BV_bound {h α s : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    (hα : 0 < α) (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => circleKernel h α (s-t) t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) * (Ico c d).indicator (fun _ => 1) s
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (h * α)⁻¹ := by
  simpa only [show (h * α)⁻¹ + 12 * (h * α)⁻¹ = 13 * (h * α)⁻¹ by ring] using
    (tested_circleEndpoint_control hh hhone hα hs a b c d).boundedVariation_sup_add_le
      (by positivity)

theorem tested_manuscriptKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
      (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        5 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, manuscript_reciprocal_height hm] using
    tested_circleKernel_BV_bound hh hhone hα hs a b c d

theorem tested_manuscriptEndpointKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (a b c d : ℝ) :
    let f := fun t => manuscriptEndpointKernel m s t *
      (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) * (Ico c d).indicator (fun _ => 1) s
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (m : ℝ) ^ (13 / 5 : ℝ) := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, manuscript_reciprocal_height hm] using
    tested_circleEndpoint_BV_bound hh hhone hα hs a b c d

theorem tested_manuscript_oriented_BV_bound_ten {m : ℕ} (hm : 200 ≤ m) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (endpoint : Bool) (a b c d : ℝ) :
    let f := fun t => if endpoint then
      manuscriptEndpointKernel m s t * (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
        (Ico c d).indicator (fun _ => 1) s
      else manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
        (Ico c d).indicator (fun _ => 1) (Int.fract (s+t))
    BoundedVariationOn f (Icc (0 : ℝ) 1) ∧
      sSup (Set.range (fun t => |f t|)) + (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤
        13 * (m : ℝ)^10 := by
  have hp : (m : ℝ) ^ (13 / 5 : ℝ) ≤ (m : ℝ)^10 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ m))
      (by norm_num)
  cases endpoint
  · simp only [Bool.false_eq_true, ite_false, if_false]
    have hb := tested_manuscriptKernel_BV_bound hm hs a b c d
    refine ⟨hb.1, hb.2.trans ?_⟩
    calc
      5 * (m : ℝ) ^ (13 / 5 : ℝ) ≤ 13 * (m : ℝ) ^ (13 / 5 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (by norm_num)
        positivity
      _ ≤ 13 * (m : ℝ)^10 := mul_le_mul_of_nonneg_left hp (by norm_num)
  · simp only [ite_true, if_true]
    have hb := tested_manuscriptEndpointKernel_BV_bound hm hs a b c d
    exact ⟨hb.1, hb.2.trans (mul_le_mul_of_nonneg_left hp (by norm_num))⟩

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTestedKernelMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductSamplingPhaseMoments
open Invariant233.ScalarSampling

@[fun_prop] theorem testedKernel_measurable (m : ℕ) (selected endpoint : Bool)
    (a b c d : ℝ) : Measurable (Function.uncurry (testedKernel m selected endpoint a b c d)) := by
  have hfirst : Measurable (Function.uncurry (TestedSampling.firstKernel m (Ico a b) (Ico c d))) :=
    ((measurable_circleKernel _ _).mul
      ((measurable_const.indicator measurableSet_Ico).comp measurable_fst)).mul
      ((measurable_const.indicator measurableSet_Ico).comp
        (measurable_fract.comp (measurable_fst.add measurable_snd)))
  have hsecond : Measurable (Function.uncurry (TestedSampling.secondKernel m (Ico a b) (Ico c d))) :=
    ((measurable_circleEndpoint_pair _ _).mul
      ((measurable_const.indicator measurableSet_Ico).comp
        (measurable_fract.comp (measurable_fst.sub measurable_snd)))).mul
      ((measurable_const.indicator measurableSet_Ico).comp measurable_fst)
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · exact hfirst
  · exact hsecond
  · exact TestedTriangular.firstKernel_measurable measurableSet_Ico measurableSet_Ico
  · exact TestedTriangular.secondKernel_measurable measurableSet_Ico measurableSet_Ico

theorem testedKernel_bounds {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d s t : ℝ) :
    0 ≤ testedKernel m selected endpoint a b c d s t ∧
      |testedKernel m selected endpoint a b c d s t| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  have hheight : 1 ≤ (m : ℝ)^(13 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have hb (s t : ℝ) : 0 ≤ manuscriptKernel m s t ∧
      manuscriptKernel m s t ≤ (m : ℝ)^(13 / 5 : ℝ) := by
    simpa only [manuscript_reciprocal_height hm, manuscriptKernel, circleKernel] using
      (rawKernel_height hh hα : 0 ≤ manuscriptKernel m s t ∧
        manuscriptKernel m s t ≤ ((m : ℝ)^(-(3 / 5 : ℝ)) * (1 / (m : ℝ)^2))⁻¹)
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · by_cases hs : s ∈ Ico a b <;> by_cases ht : Int.fract (s+t) ∈ Ico c d <;>
      simp [TestedSampling.firstKernel, hs, ht, (hb s t).1, abs_of_nonneg (hb s t).1,
        (hb s t).2, hheight.trans' zero_le_one]
  · by_cases hs : Int.fract (s-t) ∈ Ico a b <;> by_cases ht : s ∈ Ico c d <;>
      simp [TestedSampling.secondKernel, manuscriptEndpointKernel, hs, ht, (hb (s-t) t).1,
        abs_of_nonneg (hb (s-t) t).1, (hb (s-t) t).2, hheight.trans' zero_le_one]
  · have h := TestedTriangular.firstKernel_bounds (Ico a b) (Ico c d) s t
    exact ⟨h.1, by rw [abs_of_nonneg h.1]; exact h.2.trans ((TestedTriangular.triangularKernel_bounds s t).2.trans hheight)⟩
  · have h := TestedTriangular.secondKernel_bounds (Ico a b) (Ico c d) s t
    exact ⟨h.1, by rw [abs_of_nonneg h.1]; exact h.2.trans ((TestedTriangular.triangularKernel_bounds (Int.fract (s-t)) t).2.trans hheight)⟩

theorem realBVSize_le_of_global {f : ℝ → ℝ} {C V : ℝ}
    (hf : ∀ t, |f t| ≤ C)
    (hsize : sSup (Set.range (fun t => |f t|)) +
      (eVariationOn f (Icc (0 : ℝ) 1)).toReal ≤ V) : realBVSize f ≤ V := by
  have hsup : sSup ((fun t => |f t|) '' Icc (0 : ℝ) 1) ≤
      sSup (Set.range (fun t => |f t|)) := by
    apply csSup_le ((nonempty_Icc.mpr zero_le_one).image _)
    rintro _ ⟨t, _, rfl⟩
    exact le_csSup ⟨C, by rintro _ ⟨t, rfl⟩; exact hf t⟩ ⟨t, rfl⟩
  dsimp only [realBVSize]
  linarith

theorem testedKernel_BV_bound {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d : ℝ) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    BoundedVariationOn (testedKernel m selected endpoint a b c d s) (Icc (0 : ℝ) 1) ∧
      realBVSize (testedKernel m selected endpoint a b c d s) ≤ 16 * (m : ℝ)^10 := by
  have hbound := fun t => (testedKernel_bounds hm selected endpoint a b c d s t).2
  have hheight : 1 ≤ (m : ℝ)^10 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ m by omega))
  cases selected
  · have h := tested_manuscript_oriented_BV_bound_ten hm hs endpoint a b c d
    have heq : testedKernel m false endpoint a b c d s =
        fun t => if endpoint then manuscriptEndpointKernel m s t *
          (Ico a b).indicator (fun _ => 1) (Int.fract (s-t)) *
          (Ico c d).indicator (fun _ => 1) s
        else manuscriptKernel m s t * (Ico a b).indicator (fun _ => 1) s *
          (Ico c d).indicator (fun _ => 1) (Int.fract (s+t)) := by
      cases endpoint <;> rfl
    rw [heq]
    refine ⟨h.1, ?_⟩
    apply (realBVSize_le_of_global (by simpa only [heq] using hbound) h.2).trans
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) 10]
  · cases endpoint
    · have h := TestedTriangular.firstKernel_interval_BV_bound (Ico a b) c d hs
      refine ⟨h.1, ?_⟩
      exact (realBVSize_le_of_global hbound h.2).trans (by nlinarith)
    · have h := TestedTriangular.secondKernel_interval_BV_bound (Ico c d) a b hs
      refine ⟨h.1, ?_⟩
      exact (realBVSize_le_of_global hbound h.2).trans (by nlinarith)

theorem testedKernel_momentBounds {m : ℕ} (hm : 200 ≤ m) (selected endpoint : Bool)
    (a b c d : ℝ) : TestedSampling.MomentBounds m (testedKernel m selected endpoint a b c d) := by
  cases selected <;> cases endpoint <;> simp only [testedKernel, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · exact TestedSampling.firstKernel_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.secondKernel_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.firstTriangular_moment_bounds hm measurableSet_Ico measurableSet_Ico
  · exact TestedSampling.secondTriangular_moment_bounds hm measurableSet_Ico measurableSet_Ico

theorem testedKernel_square_moment_bound {m : ℕ} (hm : 200 ≤ m)
    (selected endpoint : Bool) (a b c d : ℝ) :
    (∫ s, ∫ t, (testedKernel m selected endpoint a b c d s t)^2
        ∂unitInterval ∂unitInterval) ≤
      (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) := by
  have hi : IntegrableOn (fun p : ℝ × ℝ =>
      (testedKernel m selected endpoint a b c d p.1 p.2)^2)
      (uIoc (0 : ℝ) 1 ×ˢ uIoc (0 : ℝ) 1) := by
    apply integrableOn_unitSquare_of_bound
      (F := fun s t => (testedKernel m selected endpoint a b c d s t)^2)
      (C := ((m : ℝ)^(13 / 5 : ℝ))^2)
      ((testedKernel_measurable m selected endpoint a b c d).pow_const 2)
    intro s t
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (testedKernel_bounds hm selected endpoint a b c d s t).2 2
  simp_rw [integral_unitInterval]
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun s t => (testedKernel m selected endpoint a b c d s t)^2) hi]
  exact (testedKernel_momentBounds hm selected endpoint a b c d).2.2.2.2.2

theorem tested_expected_average_error_le {κ : Type*} [Fintype κ]
    {p : ProductScaleData} (hp : ProductScaleLaws p) {j : ℕ} (hm : 200 ≤ p.m j)
    (N₀ : κ → ℝ) (hN : ∀ i, 0 < N₀ i) (hNle : ∀ i, N₀ i ≤ p.N j)
    (powers : Finset ℕ) (hs : ProductSamplingPowersAt p j powers)
    (selected : κ → Bool) (endpoint : Bool) (a b c d : κ → ℝ) :
    let u := fun i => testedKernel (p.m j) (selected i) endpoint (a i) (b i) (c i) (d i)
    (∫ θ, ∫ x, ((powers.card : ℝ)⁻¹ *
        (∑ n ∈ powers, ∏ i, u i (x i) (Int.fract ((n : ℝ) * θ i))) -
        ∏ i, mean (u i) (x i))^2
      ∂Measure.pi (fun _ : κ => unitInterval)
      ∂Measure.pi (fun i => UniformIntervalPhase.lambdaLaw (N₀ i))) ≤
      (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^Fintype.card κ /
          (powers.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
          (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
            (p.m j : ℝ)^(-50 : ℝ))^(Fintype.card κ - 1)) := by
  dsimp only
  let u := fun i => testedKernel (p.m j) (selected i) endpoint (a i) (b i) (c i) (d i)
  have h := expected_average_error_le_source_scale hp hm N₀ hN hNle powers hs u
    (fun _ => (p.m j : ℝ)^(13 / 5 : ℝ))
    (fun i => testedKernel_measurable _ _ _ _ _ _ _)
    (fun i s t => (testedKernel_bounds hm _ _ _ _ _ _ s t).2)
    (fun i s t => (testedKernel_bounds hm _ _ _ _ _ _ s t).1)
    (fun i s => by
      simpa only [mean, integral_unitInterval] using
        ((testedKernel_momentBounds hm (selected i) endpoint (a i) (b i) (c i) (d i)).2.2.1 s).2)
    (fun i s hs => (testedKernel_BV_bound hm _ _ _ _ _ _ hs).1)
    (fun i s hs => (testedKernel_BV_bound hm _ _ _ _ _ _ hs).2)
    (fun i => by
      simpa only [mean, integral_unitInterval] using
        (testedKernel_momentBounds hm (selected i) endpoint (a i) (b i) (c i) (d i)).2.2.2.1.2)
    (fun i => testedKernel_square_moment_bound hm (selected i) endpoint (a i) (b i) (c i) (d i))
  apply h.trans
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg powers.card)
  apply pow_le_pow_left₀ _ (ScalarSampling.twice_kernel_square_mass_le hm)
  have hraw := TestedSampling.half_le_common_square_bound hm
  linarith

end Invariant233.ProductSamplingPhaseMoments

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingAlmostSure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233.ProductSampling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_summable_of_lintegral_tsum_ne_top {e : ℕ → Ω → ℝ}
    (he : ∀ n ω, 0 ≤ e n ω)
    (hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (e n ω)) μ)
    (hsum : (∑' n, ∫⁻ ω, ENNReal.ofReal (e n ω) ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, Summable (fun n => e n ω) := by
  have hfinite : ∀ᵐ ω ∂μ, (∑' n, ENNReal.ofReal (e n ω)) < ∞ := by
    apply ae_lt_top' (AEMeasurable.tsum hmeas)
    rwa [lintegral_tsum hmeas]
  filter_upwards [hfinite] with ω hω
  simpa only [ENNReal.toReal_ofReal (he _ _)] using ENNReal.summable_toReal hω.ne

end Invariant233.ProductSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductInfiniteSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace Invariant233.ProductSampling

theorem measurePreserving_finset_restrict
    {κ : Type*} {X : κ → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : κ) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (D : Finset κ) :
    MeasurePreserving D.restrict (Measure.infinitePi μ)
      (Measure.pi (fun i : D => μ i)) :=
  ⟨by fun_prop, Measure.infinitePi_map_restrict μ⟩

theorem ae_summable_spatial_integral_sq_of_summable_bound
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ℕ → Ω → X → ℝ) (b : ℕ → ℝ)
    (hsq : ∀ n, Integrable (fun p : Ω × X => (F n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ n, (∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ) ≤ b n)
    (hb : Summable b) :
    ∀ᵐ a ∂μ, Summable (fun n => ∫ x, (F n a x) ^ 2 ∂ν) := by
  let e : ℕ → Ω → ℝ := fun n a => ∫ x, (F n a x) ^ 2 ∂ν
  have he : ∀ n a, 0 ≤ e n a := fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have hi : ∀ n, Integrable (e n) μ := fun n => (hsq n).integral_prod_left
  have hlin : ∀ n, (∫⁻ a, ENNReal.ofReal (e n a) ∂μ) ≤ ENNReal.ofReal (b n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall (he n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact ae_summable_of_lintegral_tsum_ne_top he
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hlin) hb.tsum_ofReal_ne_top.lt_top))

theorem ae_memLp_and_tendsto_norm_of_summable_expected_sq
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {ν : Measure X} [SFinite μ] [SFinite ν]
    (F : ℕ → Ω → X → ℝ) (b : ℕ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun p : Ω × X => F n p.1 p.2) (μ.prod ν))
    (hsq : ∀ n, Integrable (fun p : Ω × X => (F n p.1 p.2) ^ 2) (μ.prod ν))
    (hbound : ∀ n, (∫ a, ∫ x, (F n a x) ^ 2 ∂ν ∂μ) ≤ b n)
    (hb : Summable b) :
    ∀ᵐ a ∂μ, ∃ hf : ∀ n, MemLp (F n a) 2 ν,
      Summable (fun n => ∫ x, (F n a x) ^ 2 ∂ν) ∧
      Tendsto (fun n => ‖(hf n).toLp (F n a)‖) atTop (𝓝 0) := by
  have hm : ∀ᵐ a ∂μ, ∀ n, MemLp (F n a) 2 ν := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [(hmeas n).prodMk_left, (hsq n).prod_right_ae] with a ha hia
    exact (memLp_two_iff_integrable_sq ha).mpr hia
  filter_upwards [hm, ae_summable_spatial_integral_sq_of_summable_bound F b hsq hbound hb]
    with a ha hsum
  refine ⟨ha, hsum, ?_⟩
  have hnorm (n : ℕ) :
      Real.sqrt (∫ x, (F n a x) ^ 2 ∂ν) = ‖(ha n).toLp (F n a)‖ := by
    have heq : ‖(ha n).toLp (F n a)‖ ^ 2 = ∫ x, (F n a x) ^ 2 ∂ν := by
      rw [InvariantRotation.SamplingMomentBounds.l2_norm_sq_eq_integral_sq]
      apply integral_congr_ae
      filter_upwards [(ha n).coeFn_toLp] with x hx
      rw [hx]
    rw [← heq, Real.sqrt_sq (norm_nonneg _)]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsum.tendsto_atTop_zero
  simpa only [Function.comp_def, hnorm, Real.sqrt_zero] using h

end Invariant233.ProductSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingCoordinateScales
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductPhases.card_consecutiveBlock _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.ProductScaleData

theorem exists_block_of_lt_prefixCount (p : ProductScaleData) (j : ℕ)
    {i : ℕ} (hi : i < p.prefixCount j) :
    ∃ s < j, i ∈ ProductPhases.consecutiveBlock p.m s := by
  induction j with
  | zero => simp [prefixCount] at hi
  | succ j ih =>
      by_cases hij : i < p.prefixCount j
      · obtain ⟨s, hs, his⟩ := ih hij
        exact ⟨s, Nat.lt_succ_of_lt hs, his⟩
      · refine ⟨j, Nat.lt_succ_self j, ?_⟩
        have hi' : i < p.prefixCount j + p.m j := by
          simpa only [prefixCount, Finset.sum_range_succ] using hi
        simpa only [ProductPhases.consecutiveBlock, Finset.mem_Ico, prefixCount]
          using And.intro (Nat.le_of_not_gt hij) hi'

end Invariant233.ProductScaleData

namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem coordinate_scale_bounds (S : ℕ → ℝ)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (j : ℕ) {i : ℕ} (hi : i < p.prefixCount (j + 1)) :
    0 < S i ∧ S i ≤ p.N j := by
  obtain ⟨s, hs, his⟩ := p.exists_block_of_lt_prefixCount (j + 1) hi
  rw [hblock s i his]
  exact ⟨mul_pos (by exact_mod_cast hp.m_pos s) (hp.real_K_pos s),
    hp.N_strictMono.monotone (Nat.lt_succ_iff.mp hs)⟩

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingErrorSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ProductSampling

theorem summable_rpow_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) {r : ℝ} (hr : r < 0) :
    Summable (fun n => m n ^ r) := by
  have hgeom : Summable (fun n : ℕ => ((2 : ℝ) ^ r) ^ n) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hr)
  apply hgeom.of_norm_bounded
  intro n
  have hm0 : 0 ≤ m n := le_trans (by positivity : 0 ≤ (2 : ℝ) ^ n) (hm n)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hm0 _)]
  calc
    m n ^ r ≤ ((2 : ℝ) ^ n) ^ r :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hm n) hr.le
    _ = ((2 : ℝ) ^ r) ^ n := by
      rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
        Real.rpow_mul_natCast (by norm_num)]

theorem summable_superpower_of_two_pow_le {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) {b : ℝ} (hb : 0 < b) :
    Summable (fun n => m n ^ (-(m n) / b)) := by
  have hrecip : Summable (fun n => m n ^ (-1 : ℝ)) :=
    summable_rpow_of_two_pow_le hm (by norm_num)
  apply hrecip.of_norm_bounded_eventually_nat
  have hlarge : ∀ᶠ n : ℕ in atTop, b ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop b
  filter_upwards [hlarge] with n hn
  have hm1 : 1 ≤ m n := le_trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (hm n)
  have hm0 : 0 ≤ m n := le_trans zero_le_one hm1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hm0 _)]
  apply Real.rpow_le_rpow_of_exponent_le hm1
  apply (div_le_iff₀ hb).mpr
  have hbmn : b ≤ m n := hn.trans (hm n)
  linarith

theorem sampling_error_majorant_summable {m : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n) (C : ℝ) :
    Summable (fun n => C * m n ^ (-39 : ℝ) + m n ^ (-(m n) / 25)) := by
  exact ((summable_rpow_of_two_pow_le hm (by norm_num : (-39 : ℝ) < 0)).mul_left C).add
    (summable_superpower_of_two_pow_le hm (by norm_num : (0 : ℝ) < 25))

end Invariant233.ProductSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingNumericalMajorant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductSampling

theorem eventually_const_mul_log_le_rpow (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℝ in atTop, c * Real.log m ≤ m ^ δ := by
  have h := ((isLittleO_log_rpow_atTop hδ).const_mul_left c).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with m hm hm0
  have habs : |c * Real.log m| ≤ m ^ δ := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg hm0 δ)] using hm
  exact (le_abs_self _).trans habs

theorem diagonal_sampling_term_le
    {c m P : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hlog : c * Real.log m ≤ m ^ (1 / 25 : ℝ))
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hP : m ^ ((69 / 100 : ℝ) * m) ≤ P) :
    (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hn0 : 0 ≤ c * m ^ (3 / 5 : ℝ) * Real.log m := by
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hm0.le _)) (Real.log_nonneg hm)
  have hbase : c * m ^ (3 / 5 : ℝ) * Real.log m ≤ m ^ (16 / 25 : ℝ) := by
    calc
      c * m ^ (3 / 5 : ℝ) * Real.log m = m ^ (3 / 5 : ℝ) * (c * Real.log m) := by ring
      _ ≤ m ^ (3 / 5 : ℝ) * m ^ (1 / 25 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hm0.le _)
      _ = m ^ (16 / 25 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num
  have hnum : (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d ≤
      m ^ ((13 / 20 : ℝ) * m) := by
    calc
      _ ≤ (m ^ (16 / 25 : ℝ)) ^ d := pow_le_pow_left₀ hn0 hbase d
      _ = m ^ ((16 / 25 : ℝ) * (d : ℝ)) := (Real.rpow_mul_natCast hm0.le _ _).symm
      _ ≤ m ^ ((13 / 20 : ℝ) * m) := by
        apply Real.rpow_le_rpow_of_exponent_le hm
        nlinarith
  have hP0 : 0 < m ^ ((69 / 100 : ℝ) * m) := Real.rpow_pos_of_pos hm0 _
  calc
    _ ≤ m ^ ((13 / 20 : ℝ) * m) / P := div_le_div_of_nonneg_right hnum (hP0.le.trans hP)
    _ ≤ m ^ ((13 / 20 : ℝ) * m) / m ^ ((69 / 100 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hm0.le _) hP0 hP
    _ = m ^ (-m / 25) := by
      rw [← Real.rpow_sub hm0]
      congr 1
      ring

theorem eventually_diagonal_sampling_term_le (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ (d : ℕ) (P : ℝ),
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P ≤ m ^ (-m / 25) := by
  filter_upwards [eventually_const_mul_log_le_rpow c (by norm_num : (0 : ℝ) < 1 / 25),
    eventually_ge_atTop (1 : ℝ)] with m hlog hm
  exact fun d P hd hP => diagonal_sampling_term_le hc hm hlog hd hP

theorem sampling_product_factor_le_exp
    {c m : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1) ≤
      Real.exp (3 * c) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let β : ℝ := c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)
  have hβ : 0 ≤ β := by dsimp [β] <;> positivity
  have hsmall (r : ℝ) (hr : r ≤ -1) : m ^ r ≤ m⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hm hr
  have hβbound : β ≤ 2 * c * m⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left (hsmall (-(6 / 5 : ℝ)) (by norm_num)) hc
    have h2 := mul_le_mul_of_nonneg_left (hsmall (-50 : ℝ) (by norm_num)) hc
    dsimp [β]
    linarith
  have hdim : (d : ℝ) * β ≤ 3 * c := by
    calc
      (d : ℝ) * β ≤ ((101 / 100 : ℝ) * m) * (2 * c * m⁻¹) :=
        mul_le_mul hd hβbound hβ (by positivity)
      _ = (101 / 50 : ℝ) * c := by field_simp <;> ring
      _ ≤ 3 * c := by linarith
  have hdm : ((d - 1 : ℕ) : ℝ) * β ≤ 3 * c := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hβ) hdim
    exact_mod_cast Nat.sub_le d 1
  have hbase : 1 + β ≤ Real.exp β := by simpa only [add_comm] using Real.add_one_le_exp β
  rw [add_assoc]
  change (1 + β) ^ (d - 1) ≤ _
  calc
    (1 + β) ^ (d - 1) ≤ (Real.exp β) ^ (d - 1) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (((d - 1 : ℕ) : ℝ) * β) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (3 * c) := Real.exp_le_exp.mpr hdm

theorem sampling_product_error_le
    {c m : ℝ} {d : ℕ} (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hd : (d : ℝ) ≤ (101 / 100 : ℝ) * m) :
    3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
      (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
      (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hfactor := sampling_product_factor_le_exp hc hm hd
  have hcancel : m * m ^ (-50 : ℝ) = m ^ (-49 : ℝ) := by
    calc
      m * m ^ (-50 : ℝ) = m ^ (1 : ℝ) * m ^ (-50 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (-49 : ℝ) := by rw [← Real.rpow_add hm0]; norm_num
  have hdim : (d : ℝ) * m ^ (-50 : ℝ) ≤ (101 / 100 : ℝ) * m ^ (-39 : ℝ) := by
    calc
      (d : ℝ) * m ^ (-50 : ℝ) ≤ ((101 / 100 : ℝ) * m) * m ^ (-50 : ℝ) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hm0.le _)
      _ = (101 / 100 : ℝ) * m ^ (-49 : ℝ) := by rw [mul_assoc, hcancel]
      _ ≤ (101 / 100 : ℝ) * m ^ (-39 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  calc
    _ ≤ 3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) * Real.exp (3 * c)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (3 * c * Real.exp (3 * c)) * ((d : ℝ) * m ^ (-50 : ℝ)) := by ring
    _ ≤ (3 * c * Real.exp (3 * c)) * ((101 / 100 : ℝ) * m ^ (-39 : ℝ)) :=
      mul_le_mul_of_nonneg_left hdim (by positivity)
    _ ≤ (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) := by
      nlinarith [mul_nonneg hc (mul_nonneg (Real.exp_pos (3 * c)).le
        (Real.rpow_nonneg hm0.le (-39 : ℝ)))]

theorem eventually_sampling_moment_majorant (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℝ in atTop, ∀ (d : ℕ) (P : ℝ),
      (d : ℝ) ≤ (101 / 100 : ℝ) * m →
      m ^ ((69 / 100 : ℝ) * m) ≤ P →
      (c * m ^ (3 / 5 : ℝ) * Real.log m) ^ d / P +
        3 * ((d : ℝ) * (c * m ^ (-50 : ℝ)) *
          (1 + c * m ^ (-(6 / 5 : ℝ)) + c * m ^ (-50 : ℝ)) ^ (d - 1)) ≤
        (4 * c * Real.exp (3 * c)) * m ^ (-39 : ℝ) + m ^ (-m / 25) := by
  filter_upwards [eventually_diagonal_sampling_term_le c hc,
    eventually_ge_atTop (1 : ℝ)] with m hdiag hm
  intro d P hd hP
  have h1 := hdiag d P hd hP
  have h2 := sampling_product_error_le hc hm hd
  linarith

theorem summable_of_sampling_moment_bound
    {m e : ℕ → ℝ} (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (c : ℝ) (hc : 0 ≤ c) (d : ℕ → ℕ) (P : ℕ → ℝ)
    (hd : ∀ᶠ n in atTop, (d n : ℝ) ≤ (101 / 100 : ℝ) * m n)
    (hP : ∀ᶠ n in atTop, (m n) ^ ((69 / 100 : ℝ) * m n) ≤ P n)
    (he : ∀ n, 0 ≤ e n)
    (herror : ∀ᶠ n in atTop,
      e n ≤ (c * (m n) ^ (3 / 5 : ℝ) * Real.log (m n)) ^ (d n) / P n +
        3 * ((d n : ℝ) * (c * (m n) ^ (-50 : ℝ)) *
          (1 + c * (m n) ^ (-(6 / 5 : ℝ)) + c * (m n) ^ (-50 : ℝ)) ^ (d n - 1))) :
    Summable e := by
  have hmTop : Tendsto m atTop atTop :=
    tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hbound := hmTop.eventually (eventually_sampling_moment_majorant c hc)
  apply (sampling_error_majorant_summable hm (4 * c * Real.exp (3 * c))).of_norm_bounded_eventually_nat
  filter_upwards [hbound, hd, hP, herror] with n hn hdn hPn hen
  rw [Real.norm_of_nonneg (he n)]
  exact hen.trans (hn (d n) (P n) hdn hPn)

end Invariant233.ProductSampling

namespace Invariant233.ProductScaleLaws

theorem summable_sampling_error_of_moment_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (s : ℕ → Finset ℕ)
    (hs : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (s n))
    (c : ℝ) (hc : 0 ≤ c) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (herror : ∀ᶠ n in atTop,
      e n ≤ (c * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
          (p.prefixCount (n + 1)) / ((s n).card : ℝ) +
        3 * ((p.prefixCount (n + 1) : ℝ) * (c * (p.m n : ℝ) ^ (-50 : ℝ)) *
          (1 + c * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
            c * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    Summable e := by
  apply ProductSampling.summable_of_sampling_moment_bound
    (m := fun n => (p.m n : ℝ)) (fun n => by exact_mod_cast hp.m_ge_pow_self n)
    c hc (fun n => p.prefixCount (n + 1)) (fun n => ((s n).card : ℝ))
    (Eventually.of_forall hp.prefix_count_succ_le) _ he herror
  exact hs.mono fun _ hn => hn.cardinality

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

open ScalarSampling

theorem measurable_triangularKernel :
    Measurable (fun p : ℝ × ℝ => triangularKernel p.1 p.2) := by
  unfold triangularKernel
  simp only [Set.indicator_apply, mem_Ioo]
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)))
    measurable_const measurable_const

theorem measurable_coordinateWeight (I : Finset ℕ) (h α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => coordinateWeight I h α i p.1 p.2) := by
  by_cases hi : i ∈ I
  · simpa only [coordinateWeight, ite_eq_left hi] using measurable_triangularKernel
  · simpa only [coordinateWeight, ite_eq_right hi] using measurable_rawKernel_pair h α

theorem coordinateWeight_bounds (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (s t : ℝ) :
    0 ≤ coordinateWeight I h α i s t ∧
      coordinateWeight I h α i s t ≤ height h α := by
  by_cases hi : i ∈ I
  · simp only [coordinateWeight, ite_eq_left hi, triangularKernel, Set.indicator_apply]
    split_ifs
    · exact ⟨zero_le_one, le_max_left _ _⟩
    · exact ⟨le_rfl, (by unfold height; positivity)⟩
  · simp only [coordinateWeight, ite_eq_right hi]
    exact ⟨(rawKernel_height hh hα).1,
      (rawKernel_height hh hα).2.trans (le_max_right _ _)⟩

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightTests
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

namespace Invariant233.ProductModel.SamplingWeights

theorem measurable_testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ)
    (h α : ℝ) (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (fun p : ℝ × ℝ => testedCoordinateWeight endpoint I h α i E F p.1 p.2) := by
  have he : Measurable (E.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hE
  have hf : Measurable (F.indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator hF
  cases endpoint
  · exact ((measurable_coordinateWeight I h α i).mul (he.comp measurable_fst)).mul
      (hf.comp (measurable_fst.add measurable_snd).fract)
  · exact (((measurable_coordinateWeight I h α i).comp
      ((measurable_fst.sub measurable_snd).fract.prodMk measurable_snd)).mul
      (he.comp (measurable_fst.sub measurable_snd).fract)).mul
      (hf.comp measurable_fst)

theorem testedCoordinateWeight_bounds (endpoint : Bool) (I : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s t : ℝ) :
    0 ≤ testedCoordinateWeight endpoint I h α i E F s t ∧
      testedCoordinateWeight endpoint I h α i E F s t ≤ height h α := by
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : (if endpoint = true then Int.fract (s - t) else s) ∈ E
  · by_cases hf : (if endpoint = true then s else Int.fract (s + t)) ∈ F
    · simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, mul_one]
      exact coordinateWeight_bounds I hh hα i _ _
    · simp only [Set.indicator_of_notMem hf, mul_zero]
      exact ⟨le_rfl, by unfold height; positivity⟩
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact ⟨le_rfl, by unfold height; positivity⟩

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTestIntegrability
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

private theorem measurable_scalarProduct_pair (D : Finset ℕ)
    (u : ℕ → ℝ → ℝ → ℝ)
    (hu : ∀ i ∈ D, Measurable (fun p : ℝ × ℝ => u i p.1 p.2)) (n : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × Base =>
      ∏ i ∈ D, u i (circleRepresentative (z.2 i)) (Int.fract ((n : ℝ) * z.1 i))) := by
  apply Finset.measurable_prod D
  intro i hi
  have hs : Measurable (fun z : (ℕ → ℝ) × Base => circleRepresentative (z.2 i)) :=
    ProductCocycle.measurable_representative.comp ((measurable_pi_apply i).comp measurable_snd)
  have ht : Measurable (fun z : (ℕ → ℝ) × Base => Int.fract ((n : ℝ) * z.1 i)) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract
  exact (hu i hi).comp (hs.prodMk ht)

theorem measurable_testedProduct_pair (endpoint : Bool) (D I : Finset ℕ) (h α : ℝ)
    (E F : ℕ → Set ℝ) (hE : ∀ i ∈ D, MeasurableSet (E i))
    (hF : ∀ i ∈ D, MeasurableSet (F i)) (n : ℕ) :
    Measurable (fun z : (ℕ → ℝ) × Base =>
      testedProduct endpoint D I h α E F z.1 n z.2) := by
  exact measurable_scalarProduct_pair D
    (fun i => testedCoordinateWeight endpoint I h α i (E i) (F i))
    (fun i hi => measurable_testedCoordinateWeight endpoint I h α i (hE i hi) (hF i hi)) n

theorem testedProduct_bounds (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    0 ≤ testedProduct endpoint D I h α E F θ n x ∧
      testedProduct endpoint D I h α E F θ n x ≤ height h α ^ D.card := by
  constructor
  · exact Finset.prod_nonneg fun i _ =>
      (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).1
  · calc
      _ ≤ ∏ _i ∈ D, height h α := Finset.prod_le_prod
        (fun i _ => (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).1)
        (fun i _ => (testedCoordinateWeight_bounds endpoint I hh hα i (E i) (F i) _ _).2)
      _ = _ := by simp

theorem memLp_testedProduct_pair (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (n : ℕ) (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (p : ℝ≥0∞) :
    MemLp (fun z : (ℕ → ℝ) × Base => testedProduct endpoint D I h α E F z.1 n z.2)
      p (ν.prod baseMeasure) := by
  apply MemLp.of_bound
    (measurable_testedProduct_pair endpoint D I h α E F hE hF n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (testedProduct_bounds endpoint D I hh hα E F z.1 n z.2).1]
  exact (testedProduct_bounds endpoint D I hh hα E F z.1 n z.2).2

theorem stronglyMeasurable_testedAverage (endpoint : Bool) (I : Finset ℕ) (h α : ℝ)
    (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    StronglyMeasurable (fun s => ∫ t in (0 : ℝ)..1,
      testedCoordinateWeight endpoint I h α i E F s t) := by
  have hm := (measurable_testedCoordinateWeight endpoint I h α i hE hF).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hm

theorem norm_testedAverage_le (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    ‖∫ t in (0 : ℝ)..1, testedCoordinateWeight endpoint I h α i E F s t‖ ≤
      height h α := by
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α := by
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
    exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb

theorem memLp_testedIdeal (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (p : ℝ≥0∞) : MemLp (testedIdeal endpoint D I h α E F) p baseMeasure := by
  have hm : Measurable (testedIdeal endpoint D I h α E F) := by
    unfold testedIdeal
    apply Finset.measurable_prod
    intro i hi
    exact (stronglyMeasurable_testedAverage endpoint I h α i (hE i hi) (hF i hi)).measurable.comp
      (ProductCocycle.measurable_representative.comp (measurable_pi_apply i))
  apply MemLp.of_bound hm.aestronglyMeasurable (height h α ^ D.card)
  filter_upwards [] with x
  unfold testedIdeal
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ D, height h α := Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun i _ => by simpa only [Real.norm_eq_abs] using
        norm_testedAverage_le endpoint I hh hα i (E i) (F i) (circleRepresentative (x i)))
    _ = _ := by simp

theorem memLp_testedAverageError_pair (endpoint : Bool) (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i ∈ D, MeasurableSet (E i)) (hF : ∀ i ∈ D, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] :
    MemLp (fun z : (ℕ → ℝ) × Base =>
      (N.card : ℝ)⁻¹ * (∑ n ∈ N, testedProduct endpoint D I h α E F z.1 n z.2) -
        testedIdeal endpoint D I h α E F z.2) 2 (ν.prod baseMeasure) := by
  exact ((memLp_finsetSum N (fun n _ =>
    memLp_testedProduct_pair endpoint D I hh hα E F hE hF n ν 2)).const_mul
      ((N.card : ℝ)⁻¹)).sub ((memLp_testedIdeal endpoint D I hh hα E F hE hF 2).comp_snd ν)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTestAlmostSure
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem memLp_sourceTestedError_pair {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (n : ℕ) :
    MemLp (fun z : (ℕ → ℝ) × Base => sourceTestedError p N endpoint I E F n z.1 z.2)
      2 (ν.prod baseMeasure) := by
  have hm : 0 < (p.m n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 100) (hp.m_ge_100 n))
  exact memLp_testedAverageError_pair endpoint (Finset.range (p.prefixCount (n + 1))) I
    (N n) (Real.rpow_pos_of_pos hm _) (by positivity) E F
    (fun i _ => hE i) (fun i _ => hF i) ν

theorem ae_sourceTestedError_of_moment_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (endpoint : Bool) (I : Finset ℕ) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (herror : ∀ᶠ n in atTop,
      (∫ θ, ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure ∂ν) ≤
        (c * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
            (p.prefixCount (n + 1)) / ((N n).card : ℝ) +
          3 * ((p.prefixCount (n + 1) : ℝ) * (c * (p.m n : ℝ) ^ (-50 : ℝ)) *
            (1 + c * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
              c * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    ∀ᵐ θ ∂ν, ∃ hf : ∀ n, MemLp (sourceTestedError p N endpoint I E F n θ) 2 baseMeasure,
      Summable (fun n => ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure) ∧
      Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N endpoint I E F n θ)‖)
        atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n =>
    ∫ θ, ∫ x, (sourceTestedError p N endpoint I E F n θ x) ^ 2 ∂baseMeasure ∂ν
  have he : ∀ n, 0 ≤ e n := fun n =>
    integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  have hsum : Summable e :=
    hp.summable_sampling_error_of_moment_bound N hN c hc e he herror
  exact ProductSampling.ae_memLp_and_tendsto_norm_of_summable_expected_sq
    (sourceTestedError p N endpoint I E F) e
    (fun n => (memLp_sourceTestedError_pair hp N endpoint I E F hE hF ν n).aestronglyMeasurable)
    (fun n => (memLp_sourceTestedError_pair hp N endpoint I E F hE hF ν n).integrable_sq)
    (fun _ => le_rfl) hsum

theorem ae_all_sourceTestedError_of_moment_bound
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (E F : ι → ℕ → Set ℝ)
    (hE : ∀ j i, MeasurableSet (E j i)) (hF : ∀ j i, MeasurableSet (F j i))
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (herror : ∀ j, ∀ᶠ n in atTop,
      (∫ θ, ∫ x, (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ x) ^ 2
        ∂baseMeasure ∂ν) ≤
        (c j * (p.m n : ℝ) ^ (3 / 5 : ℝ) * Real.log (p.m n)) ^
            (p.prefixCount (n + 1)) / ((N n).card : ℝ) +
          3 * ((p.prefixCount (n + 1) : ℝ) * (c j * (p.m n : ℝ) ^ (-50 : ℝ)) *
            (1 + c j * (p.m n : ℝ) ^ (-(6 / 5 : ℝ)) +
              c j * (p.m n : ℝ) ^ (-50 : ℝ)) ^ (p.prefixCount (n + 1) - 1))) :
    ∀ᵐ θ ∂ν, ∀ j, ∃ hf : ∀ n,
      MemLp (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ) 2 baseMeasure,
      Summable (fun n => ∫ x,
        (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ x) ^ 2 ∂baseMeasure) ∧
      Tendsto (fun n => ‖(hf n).toLp
        (sourceTestedError p N (endpoint j) (I j) (E j) (F j) n θ)‖) atTop (𝓝 0) := by
  exact ae_all_iff.mpr fun j => ae_sourceTestedError_of_moment_bound hp N hN
    (endpoint j) (I j) (E j) (F j) (hE j) (hF j) ν (c j) (hc j) (herror j)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightScalarBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.ProductModel.SamplingWeights
open ScalarSampling

theorem testedCoordinateWeight_first_eq_scalar (I : Finset ℕ) (m i : ℕ)
    (E F : Set ℝ) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight false I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i E F s t =
      if i ∈ I then TestedTriangular.firstKernel E F s t
      else TestedSampling.firstKernel m E F s t := by
  by_cases hi : i ∈ I
  · simp [testedCoordinateWeight, coordinateWeight, TestedTriangular.firstKernel, hi]
  · simp [testedCoordinateWeight, coordinateWeight, TestedSampling.firstKernel,
      manuscriptKernel, ScalarSampling.circleKernel, Int.fract_eq_self.mpr hs,
      Int.fract_eq_self.mpr ht, hi]

theorem testedCoordinateWeight_second_eq_scalar (I : Finset ℕ) (m i : ℕ)
    (E F : Set ℝ) (s : ℝ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight true I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i E F s t =
      if i ∈ I then TestedTriangular.secondKernel E F s t
      else TestedSampling.secondKernel m E F s t := by
  by_cases hi : i ∈ I
  · simp [testedCoordinateWeight, coordinateWeight, TestedTriangular.secondKernel, hi]
  · simp [testedCoordinateWeight, coordinateWeight, TestedSampling.secondKernel,
      manuscriptEndpointKernel, manuscriptKernel, ScalarSampling.circleKernel,
      Int.fract_eq_self.mpr ht, hi]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingExpectedTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights
open ProductSamplingPhaseMoments

theorem testedCoordinateWeight_eq_testedKernel (endpoint : Bool)
    (I : Finset ℕ) (m i : ℕ) (a b c d : ℝ) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i (Ico a b) (Ico c d) s t =
    testedKernel m (decide (i ∈ I)) endpoint a b c d s t := by
  cases endpoint
  · rw [testedCoordinateWeight_first_eq_scalar I m i _ _ hs ht]
    by_cases hi : i ∈ I <;> simp [testedKernel, hi]
  · rw [testedCoordinateWeight_second_eq_scalar I m i _ _ s ht]
    by_cases hi : i ∈ I <;> simp [testedKernel, hi]

theorem testedAverage_eq_kernel_mean (endpoint : Bool)
    (I : Finset ℕ) (m i : ℕ) (a b c d : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1,
      testedCoordinateWeight endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        i (Ico a b) (Ico c d) s t) =
      mean (testedKernel m (decide (i ∈ I)) endpoint a b c d) s := by
  rw [← integral_unitInterval]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  exact testedCoordinateWeight_eq_testedKernel endpoint I m i a b c d hs ht

theorem measurePreserving_finite_representatives (D : Finset ℕ) :
    MeasurePreserving (fun x : Base => fun i : D => circleRepresentative (x i))
      baseMeasure (Measure.pi (fun _ : D => unitInterval)) := by
  exact (measurePreserving_pi (fun _ : D => circleMeasure)
    (fun _ : D => unitInterval)
    (fun _ => CocycleSupport.measurePreserving_circleRepresentative)).comp
      (ProductSampling.measurePreserving_finset_restrict (fun _ : ℕ => circleMeasure) D)

theorem integral_angle_circle_eq_finite_unit
    (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (D : Finset ℕ) (G : (D → ℝ) → (D → ℝ) → ℝ)
    (hG : Measurable (Function.uncurry G)) :
    (∫ θ, ∫ x, G (D.restrict θ) (fun i => circleRepresentative (x i))
      ∂baseMeasure ∂Measure.infinitePi μ) =
    ∫ θ, ∫ x, G θ x ∂Measure.pi (fun _ : D => unitInterval)
      ∂Measure.pi (fun i : D => μ i) := by
  have hinner (θ : ℕ → ℝ) :
      (∫ x, G (D.restrict θ) (fun i => circleRepresentative (x i)) ∂baseMeasure) =
      ∫ x, G (D.restrict θ) x ∂Measure.pi (fun _ : D => unitInterval) := by
    have hm : Measurable (G (D.restrict θ)) :=
      hG.comp (measurable_const.prodMk measurable_id)
    have he := integral_map (measurePreserving_finite_representatives D).measurable.aemeasurable
      (show AEStronglyMeasurable (G (D.restrict θ))
        (baseMeasure.map (fun x : Base => fun i : D => circleRepresentative (x i))) by
        rw [(measurePreserving_finite_representatives D).map_eq]
        exact hm.aestronglyMeasurable)
    simpa only [(measurePreserving_finite_representatives D).map_eq] using he.symm
  simp_rw [hinner]
  exact integral_restrict_infinitePi μ (s := D)
    (f := fun θ => ∫ x, G θ x ∂Measure.pi (fun _ : D => unitInterval))
    hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

theorem testedAverageError_expected_eq (m : ℕ) (D I N : Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool)
    (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      ((N.card : ℝ)⁻¹ * (∑ n ∈ N,
        testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x) -
        testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i => UniformIntervalPhase.lambdaLaw (S i))) =
      testedExpectedError m (fun i : D => S i) N (fun i : D => decide ((i : ℕ) ∈ I))
        endpoint (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) := by
  let (i : ℕ) : IsProbabilityMeasure (UniformIntervalPhase.lambdaLaw (S i)) :=
    UniformIntervalPhase.lambdaLaw_probability (S i) (hS i)
  let u : D → ℝ → ℝ → ℝ := fun i =>
    testedKernel m (decide ((i : ℕ) ∈ I)) endpoint (a i) (b i) (c i) (d i)
  let G : (D → ℝ) → (D → ℝ) → ℝ := fun θ x =>
    ((N.card : ℝ)⁻¹ * (∑ n ∈ N, ∏ i : D,
      u i (x i) (Int.fract ((n : ℝ) * θ i))) - ∏ i : D, mean (u i) (x i))^2
  have hu (i : D) : Measurable (Function.uncurry (u i)) :=
    testedKernel_measurable m _ endpoint _ _ _ _
  have hG : Measurable (Function.uncurry G) := by
    have hv (n : ℕ) : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
        ∏ i : D, u i (z.2 i) (Int.fract ((n : ℝ) * z.1 i))) := by
      apply Finset.measurable_prod
      intro i _
      have hx : Measurable (fun z : (D → ℝ) × (D → ℝ) => z.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have ht : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
          Int.fract ((n : ℝ) * z.1 i)) :=
        ((measurable_const_mul (n : ℝ)).comp
          ((measurable_pi_apply i).comp measurable_fst)).fract
      exact (hu i).comp (hx.prodMk ht)
    have hz : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
        ∏ i : D, mean (u i) (z.2 i)) := by
      apply Finset.measurable_prod
      intro i _
      exact (measurable_mean (hu i)).comp ((measurable_pi_apply i).comp measurable_snd)
    exact ((measurable_const.mul (Finset.measurable_sum N (fun n _ => hv n))).sub hz).pow_const 2
  have hprod (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
      testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x =
      ∏ i : D, u i (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
    rw [testedProduct, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    exact testedCoordinateWeight_eq_testedKernel endpoint I m i _ _ _ _
      (ProductCocycle.representative_mem_Ico (x i))
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hideal (x : Base) :
      testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x =
      ∏ i : D, mean (u i) (circleRepresentative (x i)) := by
    rw [testedIdeal, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    exact testedAverage_eq_kernel_mean endpoint I m i _ _ _ _
      (ProductCocycle.representative_mem_Ico (x i))
  simp_rw [hprod, hideal]
  exact integral_angle_circle_eq_finite_unit
    (fun i => UniformIntervalPhase.lambdaLaw (S i)) D G hG

theorem testedAverageError_expected_cond_eq (m : ℕ) (D I N : Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool)
    (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      ((N.card : ℝ)⁻¹ * (∑ n ∈ N,
        testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x) -
        testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) =
      testedExpectedError m (fun i : D => S i) N (fun i : D => decide ((i : ℕ) ∈ I))
        endpoint (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) := by
  have h := testedAverageError_expected_eq m D I N S hS endpoint a b c d
  simpa only [UniformIntervalPhase.lambdaLaw_eq_cond _ (hS _)] using h

theorem sourceTestedError_expected_eq (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool) (I : Finset ℕ)
    (a b c d : ℕ → ℝ) (j : ℕ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) =
    testedExpectedError (p.m j)
      (fun i : Finset.range (p.prefixCount (j + 1)) => S i) (N j)
      (fun i => decide ((i : ℕ) ∈ I)) endpoint
      (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) :=
  testedAverageError_expected_cond_eq (p.m j) (Finset.range (p.prefixCount (j + 1)))
    I (N j) S hS endpoint a b c d

theorem sourceTestedError_expected_le {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) {j : ℕ} (hm : 200 ≤ p.m j)
    (hN : ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ i < p.prefixCount (j + 1), S i ≤ p.N j)
    (endpoint : Bool) (I : Finset ℕ) (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) ≤
    (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^(p.prefixCount (j + 1)) /
      ((N j).card : ℝ) +
    3 * ((p.prefixCount (j + 1) : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
      (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
        (p.m j : ℝ)^(-50 : ℝ))^(p.prefixCount (j + 1) - 1)) := by
  rw [sourceTestedError_expected_eq p N S hS endpoint I a b c d j]
  have h := tested_expected_average_error_le (κ := Finset.range (p.prefixCount (j + 1)))
    hp hm (fun i => S i) (fun i => hS i)
    (fun i => hSle i (Finset.mem_range.mp i.property)) (N j) hN
    (fun i => decide ((i : ℕ) ∈ I)) endpoint
    (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i)
  simpa only [testedExpectedError, Fintype.card_coe, Finset.card_range] using h

theorem sourceTestedError_expected_le_common {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) {j : ℕ} (hm : 200 ≤ p.m j)
    (hN : ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ i < p.prefixCount (j + 1), S i ≤ p.N j)
    (endpoint : Bool) (I : Finset ℕ) (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) ≤
    (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^(p.prefixCount (j + 1)) /
      ((N j).card : ℝ) +
    3 * ((p.prefixCount (j + 1) : ℝ) * (8 * (p.m j : ℝ)^(-50 : ℝ)) *
      (1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
        8 * (p.m j : ℝ)^(-50 : ℝ))^(p.prefixCount (j + 1) - 1)) := by
  apply (sourceTestedError_expected_le hp N hm hN S hS hSle endpoint I a b c d).trans
  have he : 0 ≤ (p.m j : ℝ)^(-50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd : 0 ≤ (p.m j : ℝ)^(-6 / 5 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he' : (p.m j : ℝ)^(-50 : ℝ) ≤ 8 * (p.m j : ℝ)^(-50 : ℝ) := by linarith
  have hb : 1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) + (p.m j : ℝ)^(-50 : ℝ) ≤
      1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) + 8 * (p.m j : ℝ)^(-50 : ℝ) := by linarith
  gcongr

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingSourceAlmostSure
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem ae_all_sourceTestedError_of_coordinate_scale_bounds
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ n i, i < p.prefixCount (n + 1) → S i ≤ p.N n)
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (a b c d : ι → ℕ → ℝ) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))),
      ∀ q, ∃ hf : ∀ n,
        MemLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)
          2 baseMeasure,
        Summable (fun n => ∫ x,
          (sourceTestedError p N (endpoint q) (I q)
            (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ x)^2
          ∂baseMeasure) ∧
        Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)‖)
          atTop (𝓝 0) := by
  let μ : ℕ → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))
  let (i : ℕ) : IsProbabilityMeasure (μ i) := by
    dsimp [μ]
    rw [← UniformIntervalPhase.lambdaLaw_eq_cond (S i) (hS i)]
    exact UniformIntervalPhase.lambdaLaw_probability (S i) (hS i)
  have hmTop : Tendsto (fun n => (p.m n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => show (2 : ℝ)^n ≤ (p.m n : ℝ) from by
      exact_mod_cast hp.m_ge_pow_self n)
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hmEv : ∀ᶠ n in atTop, 200 ≤ p.m n := by
    filter_upwards [hmTop.eventually_ge_atTop 200] with n hn
    exact_mod_cast hn
  apply ae_all_sourceTestedError_of_moment_bound hp N hN endpoint I
    (fun q i => Ico (a q i) (b q i)) (fun q i => Ico (c q i) (d q i))
    (fun _ _ => measurableSet_Ico) (fun _ _ => measurableSet_Ico)
    (Measure.infinitePi μ) (fun _ => 8) (fun _ => by norm_num)
  intro q
  filter_upwards [hN, hmEv] with n hn hm
  simpa only [μ, neg_div] using sourceTestedError_expected_le_common hp N hm hn S hS (hSle n)
    (endpoint q) (I q) (a q) (b q) (c q) (d q)

theorem ae_all_sourceTestedError
    {ι : Type*} [Countable ι] {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ n in atTop, ProductSamplingPowersAt p n (N n))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ s, ∀ i ∈ ProductPhases.consecutiveBlock p.m s,
      S i = (p.m s : ℝ) * p.K s)
    (endpoint : ι → Bool) (I : ι → Finset ℕ) (a b c d : ι → ℕ → ℝ) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i))),
      ∀ q, ∃ hf : ∀ n,
        MemLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)
          2 baseMeasure,
        Summable (fun n => ∫ x,
          (sourceTestedError p N (endpoint q) (I q)
            (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ x)^2
          ∂baseMeasure) ∧
        Tendsto (fun n => ‖(hf n).toLp (sourceTestedError p N (endpoint q) (I q)
          (fun i => Ico (a q i) (b q i)) (fun i => Ico (c q i) (d q i)) n θ)‖)
          atTop (𝓝 0) :=
  ae_all_sourceTestedError_of_coordinate_scale_bounds hp N hN S hS
    (fun n _ hi => (hp.coordinate_scale_bounds S hblock n hi).2) endpoint I a b c d

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingUnitTests
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.ProductModel.SamplingWeights

theorem testedCoordinateWeight_univ_eq_Ico (endpoint : Bool)
    (I : Finset ℕ) (h α : ℝ) (i : ℕ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    testedCoordinateWeight endpoint I h α i univ univ s t =
      testedCoordinateWeight endpoint I h α i (Ico 0 1) (Ico 0 1) s t := by
  have hadd : Int.fract (s + t) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hsub : Int.fract (s - t) ∈ Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  cases endpoint <;> simp [testedCoordinateWeight, hs, hadd, hsub]

theorem testedProduct_univ_eq_Ico (endpoint : Bool) (D I : Finset ℕ)
    (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    testedProduct endpoint D I h α (fun _ => univ) (fun _ => univ) θ n x =
      testedProduct endpoint D I h α (fun _ => Ico 0 1) (fun _ => Ico 0 1) θ n x := by
  apply Finset.prod_congr rfl
  intro i _
  exact testedCoordinateWeight_univ_eq_Ico endpoint I h α i
    (ProductCocycle.representative_mem_Ico (x i)) _

theorem testedIdeal_univ_eq_Ico (endpoint : Bool) (D I : Finset ℕ)
    (h α : ℝ) (x : Base) :
    testedIdeal endpoint D I h α (fun _ => univ) (fun _ => univ) x =
      testedIdeal endpoint D I h α (fun _ => Ico 0 1) (fun _ => Ico 0 1) x := by
  apply Finset.prod_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t _
  exact testedCoordinateWeight_univ_eq_Ico endpoint I h α i
    (ProductCocycle.representative_mem_Ico (x i)) t

theorem sourceTestedError_univ_eq_Ico (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (j : ℕ) (θ : ℕ → ℝ) :
    sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ =
      sourceTestedError p N endpoint I (fun _ => Ico 0 1) (fun _ => Ico 0 1) j θ := by
  funext x
  simp only [sourceTestedError, testedProduct_univ_eq_Ico, testedIdeal_univ_eq_Ico]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSourceSamplingEnergy
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem ae_all_source_univ_energy_tendsto_zero_oai
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (hN : ∀ᶠ j in atTop, ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / S i) (2 / S i))),
      ∀ (I : Finset ℕ) (endpoint : Bool),
      Tendsto (fun j => ∫ x,
        (sourceTestedError p N endpoint I (fun _ => univ)
          (fun _ => univ) j θ x)^2 ∂baseMeasure) atTop (𝓝 0) := by
  have hall := ae_all_sourceTestedError (ι := Finset ℕ × Bool) hp N hN S hS hblock
    Prod.snd Prod.fst (fun _ _ => 0) (fun _ _ => 1)
    (fun _ _ => 0) (fun _ _ => 1)
  filter_upwards [hall] with θ hθ
  intro I endpoint
  obtain ⟨hf, hsum, hnorm⟩ := hθ (I, endpoint)
  simpa only [sourceTestedError_univ_eq_Ico] using hsum.tendsto_atTop_zero

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero_oai := @OAI.Invariant233.ProductModel.SamplingWeights.ae_all_source_univ_energy_tendsto_zero_oai
