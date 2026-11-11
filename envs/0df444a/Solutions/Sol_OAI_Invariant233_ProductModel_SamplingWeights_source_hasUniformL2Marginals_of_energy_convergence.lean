-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:33:14.72337+00:00
-- url     : https://prove2.me/submissions/7587bf34-0151-4233-a939-db99cd22cc24

import Mathlib
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

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
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ
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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RealDensityLp
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.DensityTransport

variable {X : Type*} [MeasurableSpace X]

lemma exists_Lp_density_of_memLp (μ ν : Measure X) {g : X → ℝ} {B : ℝ}
    (hg : MemLp g 2 μ) (hn : 0 ≤ᵐ[μ] g)
    (heq : ν = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (hB : 0 ≤ B) (hb : eLpNorm g 2 μ ≤ ENNReal.ofReal B) :
    ∃ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] (f : X → ℝ)) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ‖f‖ ≤ B := by
  refine ⟨hg.toLp g, ?_, ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp, hn] with x hx hnx
    simpa only [hx] using hnx
  · rw [heq]
    apply withDensity_congr_ae
    exact hg.coeFn_toLp.mono (fun x hx => congrArg ENNReal.ofReal hx.symm)
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal hB)

end Invariant233.DensityTransport

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
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem all_kernel_estimates : AllKernelEstimates := by
  intro m hm
  exact ⟨manuscriptKernel_estimates hm, manuscriptEndpointKernel_estimates hm⟩

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarKernelMomentRates
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

theorem KernelEstimates.average_square_rate {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
      1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  have hh := manuscript_width_le_half hm
  have hnonneg : 0 ≤ (m : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hden : (1 / 4 : ℝ) ≤ (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by nlinarith
  have hdenpos : 0 < (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := lt_of_lt_of_le (by norm_num) hden
  have hrate : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
      (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      4 * ((m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
    apply (div_le_iff₀ hdenpos).2
    nlinarith [mul_nonneg (sq_nonneg ((m : ℝ)^(-(3 / 5 : ℝ))))
      (sub_nonneg.mpr hden)]
  have hpow : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg m)]
    congr 1
    norm_num
  calc
    _ ≤ 1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := hu.average_square_upper
    _ ≤ 1 + 4 * ((m : ℝ)^(-(3 / 5 : ℝ)))^2 := by linarith [hrate]
    _ = _ := by rw [hpow]

theorem manuscript_average_square_rates {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) ∧
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m s v)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) :=
  ⟨(all_kernel_estimates m hm).1.average_square_rate hm,
    (all_kernel_estimates m hm).2.average_square_rate hm⟩

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductDensity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.ProductDensity

theorem integral_partial_product
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ι) → Ω i → ℝ} (s : Finset ι)
    (hh : ∀ i, Integrable (h i) (μ i)) :
    (∫ x, ∏ i ∈ s, h i (x i) ∂Measure.infinitePi μ) =
      ∏ i ∈ s, ∫ x, h i x ∂μ i := by
  rw [partial_product_eq_restrict h s]
  change (∫ x, (fun y : (i : s) → Ω i => ∏ i : s, h i (y i)) (s.restrict x)
    ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi (μ := μ) (s := s)
    (f := fun y : (i : s) → Ω i => ∏ i : s, h i (y i))
    (Integrable.fintype_prod_dep (fun i : s => hh i)).aestronglyMeasurable]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort s (fun i => ∫ x, h i x ∂μ i)

end Invariant233.ProductDensity

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

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedGraphMarginals
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.WeightedGraphMarginals

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_snd_graph (μ : Measure X) {T : X → Y} (hT : Measurable T) :
    (μ.map (fun x => (x, T x))).map Prod.snd = μ.map T := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map measurable_snd hg]
  rfl

theorem map_withDensity_inverse (μ : Measure X) {T S : X → X}
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : ∀ x, S (T x) = x) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map T = μ.withDensity (fun y => f (S y)) := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs,
    withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hT.measurable hs), ← lintegral_indicator hs]
  have h := hT.lintegral_comp ((hf.comp hS).indicator hs)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply lintegral_congr <;> intro x <;> simp only [Set.indicator, Function.comp_apply, Set.mem_preimage, hST])
  all_goals rfl

end Invariant233.WeightedGraphMarginals

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem rotationIterate_inverse_left (θ : ℕ → ℝ) (k : ℤ) (x : Base) :
    rotationIterate θ (-k) (rotationIterate θ k x) = x := by
  change ProductCocycle.rotate θ (-k) (ProductCocycle.rotate θ k x) = x
  rw [← ProductCocycle.rotate_add, add_neg_cancel, ProductCocycle.rotate_zero]

theorem orbitPairMeasure_first_marginal (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) :
    (orbitPairMeasure θ n w).map Prod.fst = baseMeasure.withDensity w := by
  exact WeightedGraphMarginals.map_fst_graph _
    (ProductCocycle.measurePreserving_rotate θ (n : ℤ)).measurable

theorem orbitPairMeasure_second_marginal (θ : ℕ → ℝ) (n : ℕ)
    (w : Base → ℝ≥0∞) (hw : Measurable w) :
    (orbitPairMeasure θ n w).map Prod.snd =
      baseMeasure.withDensity (fun y => w (rotationIterate θ (-(n : ℤ)) y)) := by
  exact (WeightedGraphMarginals.map_snd_graph (baseMeasure.withDensity w)
    (T := rotationIterate θ (n : ℤ))
    (ProductCocycle.measurePreserving_rotate θ (n : ℤ)).measurable).trans
    (WeightedGraphMarginals.map_withDensity_inverse baseMeasure
      (ProductCocycle.measurePreserving_rotate θ (n : ℤ))
      (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))).measurable
      (rotationIterate_inverse_left θ (n : ℤ)) hw)

theorem orbitAverageMeasure_first_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n)) :
    (orbitAverageMeasure θ N w).map Prod.fst =
      baseMeasure.withDensity (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) := by
  rw [orbitAverageMeasure, Measure.map_smul,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_fst]
  simp_rw [orbitPairMeasure_first_marginal]
  rw [show (fun x => (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, w n x) =
    (N.card : ℝ≥0∞)⁻¹ • (fun x => ∑ n ∈ N, w n x) from rfl,
    withDensity_smul _ (Finset.measurable_sum N hw),
    WeightedGraphMarginals.withDensity_finset_sum baseMeasure N w hw]

theorem orbitAverageMeasure_second_marginal (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n)) :
    (orbitAverageMeasure θ N w).map Prod.snd =
      baseMeasure.withDensity (fun y => (N.card : ℝ≥0∞)⁻¹ *
        ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) := by
  rw [orbitAverageMeasure, Measure.map_smul,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_snd]
  have hwi (n : ℕ) (hn : n ∈ N) :
      Measurable (fun y => w n (rotationIterate θ (-(n : ℤ)) y)) :=
    (hw n hn).comp (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))).measurable
  rw [show (fun y => (N.card : ℝ≥0∞)⁻¹ *
      ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) =
    (N.card : ℝ≥0∞)⁻¹ •
      (fun y => ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y)) from rfl,
    withDensity_smul _ (Finset.measurable_sum N hwi),
    WeightedGraphMarginals.withDensity_finset_sum baseMeasure N _ hwi]
  congr 1
  exact Finset.sum_congr rfl fun n hn => orbitPairMeasure_second_marginal θ n (w n) (hw n hn)

theorem ofReal_average_eq (N : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ N, 0 ≤ w n) :
    ENNReal.ofReal ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n) =
      (N.card : ℝ≥0∞)⁻¹ * ∑ n ∈ N, ENNReal.ofReal (w n) := by
  rcases N.eq_empty_or_nonempty with rfl | hN
  · simp
  have hc : 0 < (N.card : ℝ) := by exact_mod_cast hN.card_pos
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg hw]

theorem orbitAverageMeasure_first_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x)) := by
  rw [orbitAverageMeasure_first_marginal θ N _ (fun n hn => (hw n hn).ennreal_ofReal)]
  congr 1
  funext x
  exact (ofReal_average_eq N (fun n => w n x) (fun n hn => hw0 n hn x)).symm

theorem orbitAverageMeasure_second_marginal_real (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) :
    (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.snd =
      baseMeasure.withDensity (fun y => ENNReal.ofReal
        ((N.card : ℝ)⁻¹ * ∑ n ∈ N, w n (rotationIterate θ (-(n : ℤ)) y))) := by
  rw [orbitAverageMeasure_second_marginal θ N _ (fun n hn => (hw n hn).ennreal_ofReal)]
  congr 1
  funext y
  exact (ofReal_average_eq N _ (fun n hn => hw0 n hn _)).symm

end Invariant233.ProductModel.TailTrimming

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitL2Marginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.TailTrimming

theorem hasUniformL2Marginals_of_average_bounds (θ : ℕ → ℝ)
    (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hw0 : ∀ l, ∀ n ∈ N l, ∀ x, 0 ≤ w l n x)
    {H : ℝ} (hH : 0 ≤ H)
    (hfirst : ∀ l, eLpNorm
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) 2 baseMeasure ≤
        ENNReal.ofReal H)
    (hsecond : ∀ l, eLpNorm
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) 2 baseMeasure ≤
        ENNReal.ofReal H) :
    HasUniformL2Marginals
      (fun l => orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) := by
  refine ⟨H, hH, ?_⟩
  intro l
  have hf : MemLp
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) 2 baseMeasure :=
    ⟨((Finset.measurable_sum _ (fun n hn => hw l n hn)).const_mul _).aestronglyMeasurable,
      lt_of_le_of_lt (hfirst l) ENNReal.ofReal_lt_top⟩
  have hg : MemLp
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) 2 baseMeasure :=
    ⟨((Finset.measurable_sum _ (fun n hn => (hw l n hn).comp
      (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))).measurable)).const_mul _).aestronglyMeasurable,
      lt_of_le_of_lt (hsecond l) ENNReal.ofReal_lt_top⟩
  have hf0 : 0 ≤ᵐ[baseMeasure]
      (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) := by
    apply Filter.Eventually.of_forall
    intro x
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n hn => hw0 l n hn x))
  have hg0 : 0 ≤ᵐ[baseMeasure]
      (fun y => ((N l).card : ℝ)⁻¹ *
        ∑ n ∈ N l, w l n (rotationIterate θ (-(n : ℤ)) y)) := by
    apply Filter.Eventually.of_forall
    intro y
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun n hn => hw0 l n hn _))
  obtain ⟨f, hf0', hfEq, hfBound⟩ := DensityTransport.exists_Lp_density_of_memLp
    baseMeasure _ hf hf0 (orbitAverageMeasure_first_marginal_real θ (N l) (w l)
      (hw l) (hw0 l)) hH (hfirst l)
  obtain ⟨g, hg0', hgEq, hgBound⟩ := DensityTransport.exists_Lp_density_of_memLp
    baseMeasure _ hg hg0 (orbitAverageMeasure_second_marginal_real θ (N l) (w l)
      (hw l) (hw0 l)) hH (hsecond l)
  exact ⟨f, g, hf0', hg0', hfEq, hgEq, hfBound, hgBound⟩

end Invariant233.ProductModel.TailTrimming

end

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

theorem K_ge_100 (n : ℕ) : 100 ≤ p.K n := by
  simpa only [hp.initial_K] using hp.K_strictMono.monotone (Nat.zero_le n)

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Invariant233.ProductSampling

theorem mul_rpow_le_one {m r : ℝ} (hm : 1 ≤ m) (hr : r ≤ -1) :
    m * m ^ r ≤ 1 := by
  have hpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    m * m ^ r = m ^ (1 + r) := by rw [Real.rpow_add hpos, Real.rpow_one]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)

end Invariant233.ProductSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeights
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
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

theorem measurable_orbitWeight (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) : Measurable (orbitWeight D I h α θ n) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp (measurable_pi_apply i)).prodMk
      measurable_const)

theorem orbitWeight_bounds (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    0 ≤ orbitWeight D I h α θ n x ∧
      orbitWeight D I h α θ n x ≤ height h α ^ D.card := by
  constructor
  · exact Finset.prod_nonneg fun i hi => (coordinateWeight_bounds I hh hα i _ _).1
  · calc
      orbitWeight D I h α θ n x ≤ ∏ _i ∈ D, height h α :=
        Finset.prod_le_prod (fun i hi => (coordinateWeight_bounds I hh hα i _ _).1)
          (fun i hi => (coordinateWeight_bounds I hh hα i _ _).2)
      _ = _ := by simp

theorem memLp_orbitWeight (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (orbitWeight D I h α θ n) p baseMeasure := by
  apply MemLp.of_bound (measurable_orbitWeight D I h α θ n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (orbitWeight_bounds D I hh hα θ n x).1]
  exact (orbitWeight_bounds D I hh hα θ n x).2

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightTests
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
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

theorem fract_sub_fract (s t : ℝ) :
    Int.fract (s - t) = Int.fract (s - Int.fract t) := by
  have he : s - Int.fract t = s - t + (⌊t⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [he, Int.fract_add_intCast]

theorem representative_inverse_rotation_fract (θ : ℕ → ℝ)
    (n : ℕ) (y : Base) (i : ℕ) :
    circleRepresentative (rotationIterate θ (-(n : ℤ)) y i) =
      Int.fract (circleRepresentative (y i) - Int.fract ((n : ℝ) * θ i)) := by
  change ProductCocycle.representative (y i +
    (((-(n : ℤ) : ℤ) : ℝ) * θ i : ℝ)) = _
  rw [ProductCocycle.representative_add, Int.cast_neg, Int.cast_natCast,
    neg_mul, ← sub_eq_add_neg, fract_sub_fract]
  rfl

theorem second_testedCoordinateWeight_eq (I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (y : Base) (i : ℕ) (E F : Set ℝ) :
    testedCoordinateWeight true I h α i E F (circleRepresentative (y i))
      (Int.fract ((n : ℝ) * θ i)) =
    if circleRepresentative (rotationIterate θ (-(n : ℤ)) y i) ∈ E ∧
        circleRepresentative (y i) ∈ F then
      coordinateWeight I h α i
        (circleRepresentative (rotationIterate θ (-(n : ℤ)) y i))
        (Int.fract ((n : ℝ) * θ i))
    else 0 := by
  rw [representative_inverse_rotation_fract]
  unfold testedCoordinateWeight
  dsimp only
  by_cases he : Int.fract (circleRepresentative (y i) - (n : ℝ) * θ i) ∈ E <;>
    by_cases hf : circleRepresentative (y i) ∈ F <;> simp [he, hf, Set.indicator_apply]

theorem second_tested_product_eq (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (E F : ℕ → Set ℝ) (y : Base) :
    (∏ i ∈ D, testedCoordinateWeight true I h α i (E i) (F i)
      (circleRepresentative (y i)) (Int.fract ((n : ℝ) * θ i))) =
    (rectangle D E F).indicator (fun xy => orbitWeight D I h α θ n xy.1)
      (rotationIterate θ (-(n : ℤ)) y, y) := by
  simp_rw [second_testedCoordinateWeight_eq]
  rw [Finset.prod_ite_zero]
  simp only [rectangle, Set.indicator_apply, Set.mem_ofPred_eq, orbitWeight]

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingIdealBounds
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedTriangular.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductSampling

theorem partial_product_sq_le_exp {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (D : Finset ι) (f : (i : ι) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) {m c : ℝ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hb : ∀ i ∈ D, (∫ x, (f i x)^2 ∂μ i) ≤ 1 + c * m^(-6 / 5 : ℝ)) :
    (∫ x, (∏ i ∈ D, f i (x i))^2 ∂Measure.infinitePi μ) ≤
      Real.exp ((101 / 100 : ℝ) * c) := by
  simp_rw [← Finset.prod_pow]
  rw [ProductDensity.integral_partial_product D (fun i => (hf i).integrable_sq)]
  have hδ : 0 ≤ c * m^(-6 / 5 : ℝ) := mul_nonneg hc (Real.rpow_nonneg (by linarith) _)
  calc
    (∏ i ∈ D, ∫ x, (f i x)^2 ∂μ i) ≤ ∏ _i ∈ D, (1 + c * m^(-6 / 5 : ℝ)) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) hb
    _ = (1 + c * m^(-6 / 5 : ℝ))^D.card := by simp
    _ ≤ (Real.exp (c * m^(-6 / 5 : ℝ)))^D.card :=
      pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp (c * m^(-6 / 5 : ℝ))) _
    _ = Real.exp ((D.card : ℝ) * (c * m^(-6 / 5 : ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((101 / 100 : ℝ) * c) := by
      apply Real.exp_le_exp.mpr
      calc
        (D.card : ℝ) * (c * m^(-6 / 5 : ℝ)) ≤
            ((101 / 100 : ℝ) * m) * (c * m^(-6 / 5 : ℝ)) := mul_le_mul_of_nonneg_right hd hδ
        _ = ((101 / 100 : ℝ) * c) * (m * m^(-6 / 5 : ℝ)) := by ring
        _ ≤ ((101 / 100 : ℝ) * c) * 1 :=
          mul_le_mul_of_nonneg_left (mul_rpow_le_one hm (by norm_num)) (by positivity)
        _ = _ := mul_one _

theorem partial_product_eLpNorm_le_exp {ι : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (D : Finset ι) (f : (i : ι) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) {m c : ℝ}
    (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hb : ∀ i ∈ D, (∫ x, (f i x)^2 ∂μ i) ≤ 1 + c * m^(-6 / 5 : ℝ)) :
    eLpNorm (fun x => ∏ i ∈ D, f i (x i)) 2 (Measure.infinitePi μ) ≤
      ENNReal.ofReal (Real.exp ((101 / 200 : ℝ) * c)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (ProductDensity.memLp_partial_product D hf)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp ((101 / 100 : ℝ) * c))^(1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (partial_product_sq_le_exp D f hf hm hc hd hb) (by positivity)
    _ = Real.exp ((101 / 200 : ℝ) * c) := by
      rw [← Real.exp_mul]; congr 1; ring

end Invariant233.ProductSampling

namespace Invariant233.ProductModel.SamplingWeights

 theorem measurable_idealCoordinate (endpoint : Bool) (I : Finset ℕ) (h α : ℝ)
    (i : ℕ) {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    Measurable (idealCoordinate endpoint I h α i E F) :=
  ScalarSampling.measurable_interval_average (measurable_testedCoordinateWeight endpoint I h α i hE hF)

 theorem idealCoordinate_nonneg (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    0 ≤ idealCoordinate endpoint I h α i E F s :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1)

 theorem norm_idealCoordinate_le (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s : ℝ) :
    ‖idealCoordinate endpoint I h α i E F s‖ ≤ height h α := by
  have hb (t : ℝ) (_ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α := by
    rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
    exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2
  simpa [idealCoordinate] using intervalIntegral.norm_integral_le_of_norm_le_const hb

 theorem memLp_idealCoordinate (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MemLp (fun x : Circle => idealCoordinate endpoint I h α i E F (circleRepresentative x))
      2 circleMeasure := by
  apply MemLp.of_bound ((measurable_idealCoordinate endpoint I h α i hE hF).comp
    ProductCocycle.measurable_representative).aestronglyMeasurable (height h α)
  exact Filter.Eventually.of_forall fun x => norm_idealCoordinate_le endpoint I hh hα i E F _

 theorem intervalIntegrable_idealCoordinate (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    IntervalIntegrable (fun s => (idealCoordinate endpoint I h α i E F s)^2) volume 0 1 := by
  apply ScalarSampling.intervalIntegrable_unit_of_measurable_bound
    ((measurable_idealCoordinate endpoint I h α i hE hF).pow_const 2)
  intro s
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_idealCoordinate_le endpoint I hh hα i E F s) 2

theorem testedCoordinateWeight_le_univ (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (E F : Set ℝ) (s t : ℝ) :
    testedCoordinateWeight endpoint I h α i E F s t ≤
      testedCoordinateWeight endpoint I h α i univ univ s t := by
  unfold testedCoordinateWeight
  simp only [Set.indicator_univ, mul_one]
  by_cases he : (if endpoint = true then Int.fract (s - t) else s) ∈ E <;>
    by_cases hf : (if endpoint = true then s else Int.fract (s + t)) ∈ F
  · simp only [Set.indicator_of_mem he, Set.indicator_of_mem hf, mul_one]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hf, mul_zero]
    exact (coordinateWeight_bounds I hh hα i _ _).1
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact (coordinateWeight_bounds I hh hα i _ _).1
  · simp only [Set.indicator_of_notMem he, mul_zero, zero_mul]
    exact (coordinateWeight_bounds I hh hα i _ _).1

 theorem intervalIntegrable_testedCoordinateWeight (endpoint : Bool) (I : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (s : ℝ) :
    IntervalIntegrable (testedCoordinateWeight endpoint I h α i E F s) volume 0 1 := by
  apply ScalarSampling.intervalIntegrable_unit_of_measurable_bound
    ((measurable_testedCoordinateWeight endpoint I h α i hE hF).comp
      (measurable_const.prodMk measurable_id))
  intro t
  change ‖testedCoordinateWeight endpoint I h α i E F s t‖ ≤ height h α
  rw [Real.norm_eq_abs, abs_of_nonneg (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).1]
  exact (testedCoordinateWeight_bounds endpoint I hh hα i E F s t).2

 theorem idealCoordinate_le_univ (endpoint : Bool) (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (s : ℝ) :
    idealCoordinate endpoint I h α i E F s ≤ idealCoordinate endpoint I h α i univ univ s := by
  exact intervalIntegral.integral_mono (by norm_num)
    (intervalIntegrable_testedCoordinateWeight endpoint I hh hα i hE hF s)
    (intervalIntegrable_testedCoordinateWeight endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ s)
    (testedCoordinateWeight_le_univ endpoint I hh hα i E F s)

theorem idealCoordinate_univ_eq_scalar (endpoint : Bool) {I : Finset ℕ} {i m : ℕ}
    (hi : i ∉ I) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s =
      ∫ t in (0 : ℝ)..1, if endpoint then ScalarSampling.manuscriptEndpointKernel m s t
        else ScalarSampling.manuscriptKernel m s t := by
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  have ht' := Int.fract_eq_self.mpr (show t ∈ Ico (0 : ℝ) 1 from ⟨ht.1.le, ht.2⟩)
  cases endpoint <;>
    simp [testedCoordinateWeight, coordinateWeight, hi, ScalarSampling.manuscriptEndpointKernel,
      ScalarSampling.manuscriptKernel, ScalarSampling.circleKernel, ht', Int.fract_eq_self.mpr hs]

theorem idealCoordinate_univ_le_one_of_mem (endpoint : Bool) {I : Finset ℕ}
    {i : ℕ} (hi : i ∈ I) (h α s : ℝ) :
    idealCoordinate endpoint I h α i univ univ s ≤ 1 := by
  have hb (t : ℝ) (_ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖testedCoordinateWeight endpoint I h α i univ univ s t‖ ≤ (1 : ℝ) := by
    simp only [testedCoordinateWeight, coordinateWeight, ite_eq_left hi,
      ScalarSampling.triangularKernel, Set.indicator_apply]
    split_ifs <;> norm_num
  have hn : ‖idealCoordinate endpoint I h α i univ univ s‖ ≤ 1 := by
    simpa [idealCoordinate] using intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact (le_abs_self _).trans hn

theorem idealCoordinate_square_integral_le (endpoint : Bool) (I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  obtain ⟨hh, _, hα, _⟩ := ScalarSampling.manuscript_parameters hm
  have htest : (∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2) ≤
      ∫ s in (0 : ℝ)..1,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2 := by
    apply intervalIntegral.integral_mono (by norm_num)
      (intervalIntegrable_idealCoordinate endpoint I hh hα i hE hF)
      (intervalIntegrable_idealCoordinate endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ)
    intro s
    exact pow_le_pow_left₀ (idealCoordinate_nonneg endpoint I hh hα i E F s)
      (idealCoordinate_le_univ endpoint I hh hα i hE hF s) 2
  apply htest.trans
  by_cases hi : i ∈ I
  · have hu : (∫ s in (0 : ℝ)..1,
        (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2) ≤ 1 := by
      have he := intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1)
        (intervalIntegrable_idealCoordinate endpoint I hh hα i MeasurableSet.univ MeasurableSet.univ)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
        (fun s => pow_le_one₀ (idealCoordinate_nonneg endpoint I hh hα i univ univ s)
          (idealCoordinate_univ_le_one_of_mem endpoint hi _ _ s))
      simpa using he
    exact hu.trans (le_add_of_nonneg_right (by positivity))
  · have he : (∫ s in (0 : ℝ)..1,
        (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i univ univ s)^2) =
        ∫ s in (0 : ℝ)..1, (∫ t in (0 : ℝ)..1,
          if endpoint then ScalarSampling.manuscriptEndpointKernel m s t else ScalarSampling.manuscriptKernel m s t)^2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro s hs
      dsimp only
      rw [idealCoordinate_univ_eq_scalar endpoint (m := m) hi ⟨hs.1.le, hs.2⟩]
    rw [he]
    cases endpoint
    · exact (ScalarSampling.manuscript_average_square_rates hm).1
    · exact (ScalarSampling.manuscript_average_square_rates hm).2

theorem integral_circleRepresentative_eq_interval (f : ℝ → ℝ) :
    (∫ x : Circle, f (circleRepresentative x) ∂circleMeasure) =
      ∫ s in (0 : ℝ)..1, f s := by
  have hr : MeasurableEmbedding (circleRepresentative : Circle → ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  calc
    _ = ∫ s in Ico (0 : ℝ) 1, f s :=
      CocycleSupport.measurePreserving_circleRepresentative.integral_comp hr f
    _ = ∫ s in Ioc (0 : ℝ) 1, f s := integral_Ico_eq_integral_Ioc
    _ = _ := (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm

 theorem idealCoordinate_circle_square_integral_le (endpoint : Bool) (I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (i : ℕ) {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    (∫ x : Circle,
      (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F
        (circleRepresentative x))^2 ∂circleMeasure) ≤
        1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  rw [integral_circleRepresentative_eq_interval (fun s =>
    (idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i E F s)^2)]
  exact idealCoordinate_square_integral_le endpoint I hm i hE hF

theorem memLp_idealProduct (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    MemLp (idealProduct endpoint D I h α E F) 2 baseMeasure :=
  ProductDensity.memLp_partial_product D
    (fun i => memLp_idealCoordinate endpoint I hh hα i (hE i) (hF i))

theorem manuscript_idealProduct_eLpNorm_le (endpoint : Bool) (D I : Finset ℕ)
    {m : ℕ} (hm : 200 ≤ m) (hd : (D.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (E F : ℕ → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ i, MeasurableSet (F i)) :
    eLpNorm (idealProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ)))
        (1 / (m : ℝ)^2) E F) 2 baseMeasure ≤
      ENNReal.ofReal (Real.exp (101 / 50 : ℝ)) := by
  obtain ⟨hh, _, hα, _⟩ := ScalarSampling.manuscript_parameters hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have he := ProductSampling.partial_product_eLpNorm_le_exp
    (μ := fun _ : ℕ => circleMeasure) D
    (fun i x => idealCoordinate endpoint I ((m : ℝ)^(-(3 / 5 : ℝ)))
      (1 / (m : ℝ)^2) i (E i) (F i) (circleRepresentative x))
    (fun i => memLp_idealCoordinate endpoint I hh hα i (hE i) (hF i))
    (c := 4) hm' (by norm_num) hd
    (fun i _ => by simpa only [neg_div] using
      idealCoordinate_circle_square_integral_le endpoint I hm i (hE i) (hF i))
  norm_num only [show (101 / 200 : ℝ) * 4 = 101 / 50 by norm_num] at he
  exact he

theorem idealProduct_eLpNorm_le_height (endpoint : Bool) (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (E F : ℕ → Set ℝ) :
    eLpNorm' (idealProduct endpoint D I h α E F) 2 baseMeasure ≤
      ENNReal.ofReal ((height h α)^D.card) := by
  have hb : ∀ᵐ x ∂baseMeasure, ‖idealProduct endpoint D I h α E F x‖ ≤ (height h α)^D.card := by
    filter_upwards [] with x
    unfold idealProduct
    rw [norm_prod]
    calc
      (∏ i ∈ D, ‖idealCoordinate endpoint I h α i (E i) (F i) (circleRepresentative (x i))‖) ≤
          ∏ _i ∈ D, height h α :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => norm_idealCoordinate_le endpoint I hh hα i (E i) (F i) _)
      _ = _ := by simp
  have hheight : 0 ≤ (height h α)^D.card := by unfold height; positivity
  calc
    _ ≤ eLpNorm' (fun _ : Base => (height h α)^D.card) 2 baseMeasure :=
      eLpNorm'_mono_ae (by norm_num)
        (hb.mono fun _ hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg hheight] using hx)
    _ = _ := by
      rw [eLpNorm'_const_of_isProbabilityMeasure _ (by norm_num), Real.enorm_of_nonneg hheight]

theorem source_idealProduct_uniform_bound {p : ProductScaleData} (hp : ProductScaleLaws p) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ j : ℕ, ∀ endpoint : Bool, ∀ I : Finset ℕ,
      ∀ E F : ℕ → Set ℝ, (∀ i, MeasurableSet (E i)) → (∀ i, MeasurableSet (F i)) →
      eLpNorm (idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) E F) 2 baseMeasure ≤
          ENNReal.ofReal H := by
  let B : ℝ := (height ((p.m 0 : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m 0 : ℝ)^2)) ^ p.prefixCount 1
  refine ⟨max (Real.exp (101 / 50 : ℝ)) B,
    (Real.exp_pos _).le.trans (le_max_left _ _), ?_⟩
  intro j endpoint I E F hE hF
  cases j with
  | zero =>
      have hm0 : (0 : ℝ) < p.m 0 := by exact_mod_cast hp.m_pos 0
      have he := idealProduct_eLpNorm_le_height endpoint (Finset.range (p.prefixCount 1)) I
        (Real.rpow_pos_of_pos hm0 (-(3 / 5 : ℝ))) (by positivity : 0 < 1 / (p.m 0 : ℝ)^2) E F
      have hmem := memLp_idealProduct endpoint (Finset.range (p.prefixCount 1)) I
        (Real.rpow_pos_of_pos hm0 (-(3 / 5 : ℝ))) (by positivity : 0 < 1 / (p.m 0 : ℝ)^2)
        E F hE hF
      rw [eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)]
      norm_num only [ENNReal.toReal_ofNat]
      simp only [Finset.card_range] at he
      exact he.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  | succ j =>
      have hm : 200 ≤ p.m (j + 1) := by
        have hK := hp.K_ge_100 j
        have hd := hp.K_double j
        have hKm := hp.m_ge_K (j + 1)
        omega
      have hd : ((Finset.range (p.prefixCount ((j + 1) + 1))).card : ℝ) ≤
          (101 / 100 : ℝ) * p.m (j + 1) := by
        simpa only [Finset.card_range] using hp.prefix_count_succ_le (j + 1)
      exact (manuscript_idealProduct_eLpNorm_le endpoint _ I hm hd E F hE hF).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end Invariant233.ProductModel.SamplingWeights

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
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingUniformL2
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ProductSampling

theorem exists_uniform_norm_bound_of_error_tendsto
    {E : Type*} [SeminormedAddCommGroup E] (f z : ℕ → E)
    {C : ℝ} (hz : ∀ n, ‖z n‖ ≤ C)
    (herr : Tendsto (fun n => ‖f n - z n‖) atTop (𝓝 0)) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n, ‖f n‖ ≤ H := by
  obtain ⟨K, hK⟩ := herr.bddAbove_range
  refine ⟨max 0 (K + C), le_max_left _ _, fun n => ?_⟩
  calc
    ‖f n‖ ≤ ‖f n - z n‖ + ‖z n‖ := norm_le_norm_sub_add _ _
    _ ≤ K + C := add_le_add (hK (Set.mem_range_self n)) (hz n)
    _ ≤ max 0 (K + C) := le_max_right _ _

theorem sqrt_integral_sq_eq_toLp_norm
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 ν) :
    Real.sqrt (∫ x, (f x) ^ 2 ∂ν) = ‖hf.toLp f‖ := by
  have heq : ‖hf.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [InvariantRotation.SamplingMomentBounds.l2_norm_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [← heq, Real.sqrt_sq (norm_nonneg _)]

theorem tendsto_norm_toLp_sub_of_integral_sq
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (f z : ℕ → X → ℝ) (hf : ∀ n, MemLp (f n) 2 ν)
    (hz : ∀ n, MemLp (z n) 2 ν)
    (herr : Tendsto (fun n => ∫ x, (f n x - z n x) ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ‖(hf n).toLp (f n) - (hz n).toLp (z n)‖) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : Real.sqrt (∫ x, (f n x - z n x) ^ 2 ∂ν) =
      ‖(hf n).toLp (f n) - (hz n).toLp (z n)‖ := by
    rw [← MemLp.toLp_sub]
    exact sqrt_integral_sq_eq_toLp_norm ((hf n).sub (hz n))
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp herr
  simpa only [Function.comp_def, hnorm, Real.sqrt_zero] using h

end Invariant233.ProductSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingWeightAssembly
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem orientedAverage_first (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (x : Base) :
    orientedAverage false D I N h α θ x =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitWeight D I h α θ n x := by
  simp only [orientedAverage, testedCoordinateWeight, Bool.false_eq_true,
    ite_false, if_false, Set.indicator_univ, mul_one, orbitWeight]

theorem orientedAverage_second (D I N : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (y : Base) :
    orientedAverage true D I N h α θ y =
      (N.card : ℝ)⁻¹ * ∑ n ∈ N,
        orbitWeight D I h α θ n (rotationIterate θ (-(n : ℤ)) y) := by
  unfold orientedAverage
  apply congrArg ((N.card : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [rectangle_univ, Set.indicator_univ] using
    second_tested_product_eq D I h α θ n (fun _ => univ) (fun _ => univ) y

theorem hasUniformL2Marginals_of_oriented_bounds
    (θ : ℕ → ℝ) (I : Finset ℕ) (D N : ℕ → Finset ℕ) (h α : ℕ → ℝ)
    (hh : ∀ l, 0 < h l) (hα : ∀ l, 0 < α l)
    {H : ℝ} (hH : 0 ≤ H)
    (hfirst : ∀ l, eLpNorm (orientedAverage false (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H)
    (hsecond : ∀ l, eLpNorm (orientedAverage true (D l) I (N l) (h l) (α l) θ)
      2 baseMeasure ≤ ENNReal.ofReal H) :
    HasUniformL2Marginals (fun l => TailTrimming.orbitAverageMeasure θ (N l)
      (fun n x => ENNReal.ofReal (orbitWeight (D l) I (h l) (α l) θ n x))) := by
  apply TailTrimming.hasUniformL2Marginals_of_average_bounds θ N
    (fun l => orbitWeight (D l) I (h l) (α l) θ)
    (fun l n _ => measurable_orbitWeight (D l) I (h l) (α l) θ n)
    (fun l n _ x => (orbitWeight_bounds (D l) I (hh l) (hα l) θ n x).1) hH
  · intro l
    simpa only [funext (orientedAverage_first (D l) I (N l) (h l) (α l) θ)] using hfirst l
  · intro l
    simpa only [funext (orientedAverage_second (D l) I (N l) (h l) (α l) θ)] using hsecond l

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSourceSamplingL2
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights

theorem memLp_orientedAverage (endpoint : Bool) (D I N : Finset ℕ)
    {h α : ℝ} (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (q : ℝ≥0∞) :
    MemLp (orientedAverage endpoint D I N h α θ) q baseMeasure := by
  cases endpoint
  · have heq : orientedAverage false D I N h α θ =
        fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitWeight D I h α θ n x := by
      funext x
      exact orientedAverage_first D I N h α θ x
    rw [heq]
    exact (memLp_finsetSum N (fun n _ => memLp_orbitWeight D I hh hα θ n q)).const_mul _
  · have heq : orientedAverage true D I N h α θ = fun y =>
        (N.card : ℝ)⁻¹ * ∑ n ∈ N,
          orbitWeight D I h α θ n (rotationIterate θ (-(n : ℤ)) y) := by
      funext y
      exact orientedAverage_second D I N h α θ y
    rw [heq]
    exact (memLp_finsetSum N (fun n _ =>
      (memLp_orbitWeight D I hh hα θ n q).comp_measurePreserving
        (ProductCocycle.measurePreserving_rotate θ (-(n : ℤ))))).const_mul _

theorem sourceTestedError_univ_eq (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (endpoint : Bool) (I : Finset ℕ) (j : ℕ) (θ : ℕ → ℝ) (x : Base) :
    sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x =
      orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I (N j)
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ x -
      idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2)
        (fun _ => univ) (fun _ => univ) x := rfl

theorem source_orientedAverage_uniform_bound
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
      (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
        ∂baseMeasure) atTop (𝓝 0)) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ endpoint : Bool, ∀ j : ℕ,
      eLpNorm (orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I
        (N j) ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ)
        2 baseMeasure ≤ ENNReal.ofReal H := by
  let f (endpoint : Bool) (j : ℕ) :=
    orientedAverage endpoint (Finset.range (p.prefixCount (j + 1))) I (N j)
      ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ
  let z (endpoint : Bool) (j : ℕ) :=
    idealProduct endpoint (Finset.range (p.prefixCount (j + 1))) I
      ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2)
      (fun _ => univ) (fun _ => univ)
  have hm (j : ℕ) : 0 < (p.m j : ℝ) := by exact_mod_cast hp.m_pos j
  have hh (j : ℕ) : 0 < (p.m j : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos (hm j) _
  have hα (j : ℕ) : 0 < 1 / (p.m j : ℝ)^2 := one_div_pos.mpr (pow_pos (hm j) 2)
  have hf (endpoint : Bool) (j : ℕ) : MemLp (f endpoint j) 2 baseMeasure :=
    memLp_orientedAverage endpoint _ I (N j) (hh j) (hα j) θ 2
  have hz (endpoint : Bool) (j : ℕ) : MemLp (z endpoint j) 2 baseMeasure :=
    memLp_idealProduct endpoint _ I (hh j) (hα j) _ _
      (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ)
  obtain ⟨B, hB, hbound⟩ := source_idealProduct_uniform_bound hp
  have hone (endpoint : Bool) : ∃ H : ℝ, 0 ≤ H ∧ ∀ j,
      eLpNorm (f endpoint j) 2 baseMeasure ≤ ENNReal.ofReal H := by
    have hzbound (j : ℕ) : ‖(hz endpoint j).toLp (z endpoint j)‖ ≤ B := by
      rw [Lp.norm_toLp]
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (hbound j endpoint I (fun _ => univ) (fun _ => univ)
          (fun _ => MeasurableSet.univ) (fun _ => MeasurableSet.univ))
      simpa only [ENNReal.toReal_ofReal hB] using hb
    have he : Tendsto (fun j => ∫ x, (f endpoint j x - z endpoint j x)^2
        ∂baseMeasure) atTop (𝓝 0) := by
      simpa only [sourceTestedError_univ_eq] using herr endpoint
    have hlim := ProductSampling.tendsto_norm_toLp_sub_of_integral_sq
      (f endpoint) (z endpoint) (hf endpoint) (hz endpoint) he
    obtain ⟨H, hH, hb⟩ := ProductSampling.exists_uniform_norm_bound_of_error_tendsto
      (fun j => (hf endpoint j).toLp (f endpoint j))
      (fun j => (hz endpoint j).toLp (z endpoint j)) hzbound hlim
    refine ⟨H, hH, fun j => ?_⟩
    rw [← ENNReal.ofReal_toReal (hf endpoint j).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Lp.norm_toLp] using hb j)
  obtain ⟨Hf, hHf, hfirst⟩ := hone false
  obtain ⟨Hg, hHg, hsecond⟩ := hone true
  refine ⟨max Hf Hg, hHf.trans (le_max_left _ _), ?_⟩
  intro endpoint j
  cases endpoint
  · exact (hfirst j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hsecond j).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

theorem source_hasUniformL2Marginals_of_energy_convergence_oai
    {p : ProductScaleData} (hp : ProductScaleLaws p) (N : ℕ → Finset ℕ)
    (θ : ℕ → ℝ) (I : Finset ℕ)
    (herr : ∀ endpoint : Bool, Tendsto (fun j => ∫ x,
      (sourceTestedError p N endpoint I (fun _ => univ) (fun _ => univ) j θ x)^2
        ∂baseMeasure) atTop (𝓝 0)) :
    HasUniformL2Marginals (fun j => TailTrimming.orbitAverageMeasure θ (N j)
      (fun n x => ENNReal.ofReal (orbitWeight (Finset.range (p.prefixCount (j + 1))) I
        ((p.m j : ℝ)^(-(3 / 5 : ℝ))) (1 / (p.m j : ℝ)^2) θ n x))) := by
  obtain ⟨H, hH, hb⟩ := source_orientedAverage_uniform_bound hp N θ I herr
  apply hasUniformL2Marginals_of_oriented_bounds θ I
    (fun j => Finset.range (p.prefixCount (j + 1))) N
    (fun j => (p.m j : ℝ)^(-(3 / 5 : ℝ))) (fun j => 1 / (p.m j : ℝ)^2)
    (fun j => Real.rpow_pos_of_pos (by exact_mod_cast hp.m_pos j) _) ?_ hH
    (hb false) (hb true)
  intro j
  have hm : 0 < (p.m j : ℝ) := by exact_mod_cast hp.m_pos j
  positivity

end Invariant233.ProductModel.SamplingWeights

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence_oai := @OAI.Invariant233.ProductModel.SamplingWeights.source_hasUniformL2Marginals_of_energy_convergence_oai
