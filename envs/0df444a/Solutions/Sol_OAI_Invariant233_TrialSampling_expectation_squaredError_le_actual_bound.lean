-- Prove2me | solution 1 for OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:43.782374+00:00
-- url     : https://prove2.me/submissions/b0dacce5-e7a8-48f3-9061-80f03b554de0

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_TrialSampling_coordinateSample_offdiag_error

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ModuloIntervalMeasure
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ModuloIntervalMeasure

open Set MeasureTheory
open scoped ENNReal

theorem integral_periodic_le_length_add_one {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x := by
  let n : ℕ := ⌈b - a⌉₊
  have hn : b ≤ a + n := by
    have := Nat.le_ceil (b - a)
    dsimp [n]
    linarith
  have hn' : (n : ℝ) ≤ b - a + 1 := by
    exact (Nat.ceil_lt_add_one (sub_nonneg.mpr hab)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + n, f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Filter.Eventually.of_forall hf) (hint' _ _)
    _ = (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h
    _ ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x :=
      mul_le_mul_of_nonneg_right hn' hmass

theorem cond_Icc_eq_cond_Ioc (a b : ℝ) :
    ProbabilityTheory.cond volume (Icc a b) = ProbabilityTheory.cond volume (Ioc a b) := by
  simp only [ProbabilityTheory.cond, Real.volume_Icc, Real.volume_Ioc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]

end Invariant233.ModuloIntervalMeasure

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_PeriodicIntervalDiscrepancy
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.PeriodicIntervalDiscrepancy

open Set MeasureTheory
open scoped ENNReal

theorem length_sub_one_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤ ∫ x in a..b, f x := by
  let n : ℕ := ⌊b - a⌋₊
  have hn : a + n ≤ b := by
    have := Nat.floor_le (sub_nonneg.mpr hab)
    dsimp [n]
    linarith
  have hn' : b - a - 1 ≤ (n : ℝ) := (Nat.sub_one_lt_floor (b - a)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (b - a - 1) * (∫ x in (0 : ℝ)..1, f x) ≤
        (n : ℝ) * (∫ x in (0 : ℝ)..1, f x) :=
      mul_le_mul_of_nonneg_right hn' hmass
    _ = ∫ x in a..a + n, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h.symm
    _ ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_interval le_rfl (le_add_of_nonneg_right (Nat.cast_nonneg n)) hn
        (Filter.Eventually.of_forall hf) (hint' _ _)

theorem abs_integral_sub_length_mul_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a ≤ b) :
    |(∫ x in a..b, f x) - (b - a) * (∫ x in (0 : ℝ)..1, f x)| ≤
      ∫ x in (0 : ℝ)..1, |f x| := by
  have hperiodAbs : Function.Periodic (fun x => |f x|) 1 := by
    intro x
    change |f (x + 1)| = |f x|
    rw [hperiod x]
  have hp : ∀ x, 0 ≤ |f x| + f x := fun x => by linarith [neg_abs_le (f x)]
  have hm : ∀ x, 0 ≤ |f x| - f x := fun x => sub_nonneg.mpr (le_abs_self (f x))
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hpu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hpl := length_sub_one_mul_integral_le
    (hperiodAbs.add hperiod) hp (hint.abs.add hint) hab
  have hmu := ModuloIntervalMeasure.integral_periodic_le_length_add_one
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  have hml := length_sub_one_mul_integral_le
    (hperiodAbs.sub hperiod) hm (hint.abs.sub hint) hab
  simp only [Pi.add_apply, Pi.sub_apply] at hpu hpl hmu hml
  rw [intervalIntegral.integral_add (hint' a b).abs (hint' a b),
    intervalIntegral.integral_add hint.abs hint] at hpu hpl
  rw [intervalIntegral.integral_sub (hint' a b).abs (hint' a b),
    intervalIntegral.integral_sub hint.abs hint] at hmu hml
  apply abs_le.mpr
  constructor <;> nlinarith

theorem integral_cond_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    (∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) =
      (b - a)⁻¹ * ∫ x in a..b, f x := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    intervalIntegral.integral_of_le hab.le, smul_eq_mul]

theorem abs_integral_cond_sub_integral_le {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hint : IntervalIntegrable f volume 0 1)
    {a b : ℝ} (hab : a < b) :
    |(∫ x, f x ∂ProbabilityTheory.cond volume (Ioc a b)) -
        (∫ x in (0 : ℝ)..1, f x)| ≤
      (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  rw [integral_cond_Ioc hab]
  calc
    |(b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x)| =
        (b - a)⁻¹ * |(∫ x in a..b, f x) -
          (b - a) * (∫ x in (0 : ℝ)..1, f x)| := by
      have heq : (b - a)⁻¹ * (∫ x in a..b, f x) - (∫ x in (0 : ℝ)..1, f x) =
          (b - a)⁻¹ * ((∫ x in a..b, f x) -
            (b - a) * (∫ x in (0 : ℝ)..1, f x)) := by
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hlen.ne', one_mul]
      rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hlen)]
    _ ≤ (b - a)⁻¹ * ∫ x in (0 : ℝ)..1, |f x| :=
      mul_le_mul_of_nonneg_left
        (abs_integral_sub_length_mul_integral_le hperiod hint hab.le)
        (inv_nonneg.mpr hlen.le)

theorem fract_comp_eqOn {E : Type*} (g : ℝ → E) :
    EqOn (fun x => g (Int.fract x)) g (Ioo 0 1) := by
  intro x hx
  change g (Int.fract x) = g x
  rw [Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]

theorem intervalIntegrable_fract_comp {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (fun x => g (Int.fract x)) volume 0 1 := by
  apply hg.congr_uIoo
  simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (fract_comp_eqOn g).symm

theorem integral_cond_Ioc_mul {f : ℝ → ℝ} {a b k : ℝ}
    (hab : a < b) (hk : 0 < k) :
    (∫ x, f (k * x) ∂ProbabilityTheory.cond volume (Ioc a b)) =
      ∫ x, f x ∂ProbabilityTheory.cond volume (Ioc (k * a) (k * b)) := by
  rw [integral_cond_Ioc hab, integral_cond_Ioc (mul_lt_mul_of_pos_left hab hk),
    intervalIntegral.integral_comp_mul_left f hk.ne', smul_eq_mul]
  rw [← mul_sub, mul_inv_rev, mul_assoc]

theorem uniform_angle_test_le {N n : ℝ} (hN : 0 < N) (hn : 0 < n)
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    |(∫ θ, g (Int.fract (n * θ))
        ∂ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) -
      (∫ t in (0 : ℝ)..1, g t)| ≤ (N / n) * ∫ t in (0 : ℝ)..1, |g t| := by
  have hab : (1 : ℝ) / N < 2 / N :=
    (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  have hperiod : Function.Periodic (fun x => g (Int.fract x)) 1 := by
    intro x
    simp only [Int.fract_add_one]
  have h := abs_integral_cond_sub_integral_le hperiod
    (intervalIntegrable_fract_comp hg) (mul_lt_mul_of_pos_left hab hn)
  have hmean : (∫ t in (0 : ℝ)..1, g (Int.fract t)) = ∫ t in (0 : ℝ)..1, g t :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn g)
  have habs : (∫ t in (0 : ℝ)..1, |g (Int.fract t)|) =
      ∫ t in (0 : ℝ)..1, |g t| :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fract_comp_eqOn (fun t => |g t|))
  have hlen : (n * (2 / N) - n * (1 / N))⁻¹ = N / n := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num]
    field_simp
  rw [hmean, habs, hlen] at h
  rw [ModuloIntervalMeasure.cond_Icc_eq_cond_Ioc,
    integral_cond_Ioc_mul (f := fun x => g (Int.fract x)) hab hn]
  exact h

end Invariant233.PeriodicIntervalDiscrepancy

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

theorem both_kernel_estimates {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    KernelEstimates m u := by
  rcases hu with rfl | rfl
  · exact manuscriptKernel_estimates hm
  · exact manuscriptEndpointKernel_estimates hm

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

theorem parameter_kernel_eq_manuscript {m : ℕ} (hm : 200 ≤ m) (z : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.kernel m z v = manuscriptKernel m z v := by
  rw [manuscriptKernel, circleKernel_eq_raw_on_unit (manuscript_parameters hm).2.1 z hv]
  unfold CircleParameterData.kernel CircleParameterData.delta CircleParameterData.kernelWidth
    rawKernel delta
  simp only [Set.indicator_apply, mem_Ioo, ite_and, one_div]

theorem parameter_orientedKernel_eq {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (z : ℝ) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    CircleParameterData.orientedKernel endpoint m z v =
      if endpoint then manuscriptEndpointKernel m z v else manuscriptKernel m z v := by
  cases endpoint <;>
    simp only [CircleParameterData.orientedKernel, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · exact parameter_kernel_eq_manuscript hm z hv
  · exact parameter_kernel_eq_manuscript hm (z - v) hv

end Invariant233.ScalarSampling

end

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

theorem kernel_average_square_remainder_le {m : ℕ} (hm : 200 ≤ m) :
    ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 ≤
      4 * (m : ℝ)^(-(6 / 5 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hhalf := manuscript_width_le_half hm
  have hwidth : 0 < (m : ℝ)^(-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hm0 _
  have hden : (1 / 4 : ℝ) ≤ (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by nlinarith
  have hsquare : ((m : ℝ)^(-(3 / 5 : ℝ)))^2 = (m : ℝ)^(-(6 / 5 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm0.le]
    congr 1
    norm_num
  calc
    _ ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 / 4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
    _ = _ := by rw [hsquare]; ring

theorem KernelEstimates.average_square_source_bound {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
      1 + 4 * (m : ℝ)^(-(6 / 5 : ℝ)) :=
  hu.average_square_upper.trans (add_le_add le_rfl (kernel_average_square_remainder_le hm))

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

theorem KernelEstimates.twice_square_mass_rate {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : KernelEstimates m u) :
    2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v^2) ≤
      8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log ((m : ℝ)^2 / 2) ≤ 2 * Real.log m := by
    calc
      _ ≤ Real.log ((m : ℝ)^2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (m : ℝ)])
      _ = _ := by rw [Real.log_pow]; norm_num
  calc
    _ = 4 * (m : ℝ)^(3 / 5 : ℝ) * Real.log ((m : ℝ)^2 / 2) := by
      rw [hu.square_mass, Real.rpow_neg hmpos.le]
      simp only [div_inv_eq_mul]
      ring
    _ ≤ (4 * (m : ℝ)^(3 / 5 : ℝ)) * (2 * Real.log m) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentAngles
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace InvariantProjection.IndependentAngles

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc a b)) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

end InvariantProjection.IndependentAngles

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingEstimates
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Invariant233.ProductSampling

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ s, |a i| ≤ B) (hb : ∀ i ∈ s, |b i| ≤ B)
    (hab : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      (s.card : ℝ) * ε * B ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai : |a i| ≤ B := ha i (Finset.mem_insert_self _ _)
      have habi : |a i - b i| ≤ ε := hab i (Finset.mem_insert_self _ _)
      have has : ∀ j ∈ s, |a j| ≤ B := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hbs : ∀ j ∈ s, |b j| ≤ B := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have habs : ∀ j ∈ s, |a j - b j| ≤ ε :=
        fun j hj => hab j (Finset.mem_insert_of_mem hj)
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simpa using habi
      have hprod : |∏ j ∈ s, b j| ≤ B ^ s.card := by
        rw [Finset.abs_prod]
        calc
          ∏ j ∈ s, |b j| ≤ ∏ _j ∈ s, B :=
            Finset.prod_le_prod (fun index _ => abs_nonneg (b index)) hbs
          _ = B ^ s.card := by simp
      have hpow : B * B ^ (s.card - 1) = B ^ s.card := by
        rw [← pow_succ', Nat.sub_add_cancel (Finset.card_pos.mpr hs)]
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
        _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
              |a i - b i| * |∏ j ∈ s, b j| := by
          simpa only [abs_mul] using abs_add_le
            (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
            ((a i - b i) * ∏ j ∈ s, b j)
        _ ≤ B * ((s.card : ℝ) * ε * B ^ (s.card - 1)) + ε * B ^ s.card := by
          exact add_le_add
            (mul_le_mul hai (ih has hbs habs) (abs_nonneg _) hB)
            (mul_le_mul habi hprod (abs_nonneg _) hε)
        _ = (s.card : ℝ) * ε * (B * B ^ (s.card - 1)) + ε * B ^ s.card := by ring
        _ = ((s.card + 1 : ℕ) : ℝ) * ε * B ^ ((s.card + 1) - 1) := by
          rw [hpow, Nat.add_sub_cancel]
          push_cast
          ring

theorem abs_prod_add_error_sub_prod_le {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  apply abs_prod_sub_prod_le s (fun i => A i + e i) A (add_nonneg hB hε) hε
  · intro i hi
    calc
      |A i + e i| ≤ |A i| + |e i| := abs_add_le _ _
      _ ≤ B + ε := add_le_add (by simpa [abs_of_nonneg (hA i hi).1] using (hA i hi).2)
        (he i hi)
  · intro i hi
    rw [abs_of_nonneg (hA i hi).1]
    exact le_trans (hA i hi).2 (le_add_of_nonneg_right hε)
  · intro i hi
    simpa using he i hi

end Invariant233.ProductSampling

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

theorem product_perturbation_bound {ι : Type*} (s : Finset ι) (A e : ι → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hAB : ∀ i ∈ s, A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  exact Invariant233.ProductSampling.abs_prod_add_error_sub_prod_le s A e hB hε
    (fun i hi => ⟨hA i hi, hAB i hi⟩) he

theorem averaged_moment_bound {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → ι → ℝ) (C : ι → ℝ) {A D ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, Q i i ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i j ≤ A + ε)
    (hcross : ∀ i ∈ s, A - ε ≤ C i) :
    ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
        2 * (s.card : ℝ)⁻¹ * (∑ i ∈ s, C i) + A ≤
      D / (s.card : ℝ) + 3 * ε := by
  classical
  let P : ℝ := s.card
  have hn : 0 < s.card := Finset.card_pos.mpr hs
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast hn
  have hP0 : P ≠ 0 := ne_of_gt hP
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, Q i j) ≤ D + (P - 1) * (A + ε) := by
    calc
      (∑ j ∈ s, Q i j) = Q i i + ∑ j ∈ s.erase i, Q i j := by
        rw [← Finset.sum_erase_add s (Q i) hi, add_comm]
      _ ≤ D + ∑ _j ∈ s.erase i, (A + ε) := by
        apply add_le_add (hdiag i hi)
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i hi j (Finset.mem_of_mem_erase hj)
          (Ne.symm (Finset.ne_of_mem_erase hj))
      _ = D + (P - 1) * (A + ε) := by
        simp [P, Finset.card_erase_of_mem hi, Nat.cast_sub (Nat.succ_le_of_lt hn)]
        ring
  have hsum : (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤
      P * D + P * (P - 1) * (A + ε) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, Q i j) ≤ ∑ _i ∈ s, (D + (P - 1) * (A + ε)) :=
        Finset.sum_le_sum hrow
      _ = P * D + P * (P - 1) * (A + ε) := by simp [P] <;> ring
  have hc : P * (A - ε) ≤ ∑ i ∈ s, C i := by
    calc
      P * (A - ε) = ∑ _i ∈ s, (A - ε) := by simp [P] <;> ring
      _ ≤ ∑ i ∈ s, C i := Finset.sum_le_sum hcross
  change (P⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, Q i j) -
    2 * P⁻¹ * (∑ i ∈ s, C i) + A ≤ D / P + 3 * ε
  calc
    _ ≤ (P⁻¹) ^ 2 * (P * D + P * (P - 1) * (A + ε)) -
        2 * P⁻¹ * (P * (A - ε)) + A := by
      have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (P⁻¹))
      have h2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * P⁻¹ by positivity)
      linarith
    _ = D / P + 3 * ε - (A + ε) / P := by field_simp <;> ring
    _ ≤ D / P + 3 * ε := sub_le_self _ (div_nonneg (add_nonneg hA hε) hP.le)

theorem norm_average_sub_sq_le {ι E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (z : E) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, ‖v i‖ ^ 2 ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) ≤ ‖z‖ ^ 2 + ε)
    (hcross : ∀ i ∈ s, ‖z‖ ^ 2 - ε ≤ inner ℝ (v i) z) :
    ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z‖ ^ 2 ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := averaged_moment_bound s hs (fun i j => inner ℝ (v i) (v j))
    (fun i => inner ℝ (v i) z) (sq_nonneg ‖z‖) hε
    (by simpa only [real_inner_self_eq_norm_sq] using hdiag) hoff hcross
  have hn : ‖(s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)‖ ^ 2 =
      ((s.card : ℝ)⁻¹) ^ 2 * (∑ i ∈ s, ∑ j ∈ s, inner ℝ (v i) (v j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [real_inner_smul_left, real_inner_smul_right, sum_inner, inner_sum]
    ring
  rw [norm_sub_sq_real, hn, real_inner_smul_left, sum_inner]
  nlinarith [h]

open MeasureTheory

theorem l2_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [pow_two]

theorem l2_coe_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (v : ι → Lp ℝ 2 μ) :
    (fun x => (∑ i ∈ s, v i) x) =ᵐ[μ] (fun x => ∑ i ∈ s, v i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (v a) (∑ i ∈ s, v i), ih] with x hx hx'
    simpa only [Pi.add_apply, hx'] using hx

theorem integral_average_sub_sq_le {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Lp ℝ 2 μ) (z : Lp ℝ 2 μ) {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  have h := norm_average_sub_sq_le s hs v z hε
    (by simpa only [l2_norm_sq_eq_integral_sq] using hdiag)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hoff)
    (by simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, mul_comm, l2_norm_sq_eq_integral_sq] using hcross)
  rw [l2_norm_sq_eq_integral_sq] at h
  have heq : (fun x => ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i) - z) x ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [Lp.coeFn_sub ((s.card : ℝ)⁻¹ • (∑ i ∈ s, v i)) z,
      Lp.coeFn_smul (s.card : ℝ)⁻¹ (∑ i ∈ s, v i), l2_coe_finset_sum s v]
      with x hsub hsmul hsum
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.smul_apply, smul_eq_mul] at hsmul
    rw [hsub, hsmul, hsum]
  rwa [integral_congr_ae heq] at h

theorem integral_average_sub_sq_le_of_memLp {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (s : Finset ι) (hs : s.Nonempty)
    (v : ι → Ω → ℝ) (z : Ω → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hz : MemLp z 2 μ)
    {D ε : ℝ} (hε : 0 ≤ ε)
    (hdiag : ∀ i ∈ s, (∫ x, (v i x) ^ 2 ∂μ) ≤ D)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (∫ x, v i x * v j x ∂μ) ≤ (∫ x, (z x) ^ 2 ∂μ) + ε)
    (hcross : ∀ i ∈ s, (∫ x, (z x) ^ 2 ∂μ) - ε ≤ ∫ x, v i x * z x ∂μ) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2 ∂μ) ≤
      D / (s.card : ℝ) + 3 * ε := by
  let V : ι → Lp ℝ 2 μ := fun i => (hv i).toLp (v i)
  let Z : Lp ℝ 2 μ := hz.toLp z
  have hV (i : ι) : (fun x => V i x) =ᵐ[μ] v i := (hv i).coeFn_toLp
  have hZ : (fun x => Z x) =ᵐ[μ] z := hz.coeFn_toLp
  have hVsq (i : ι) : (∫ x, (V i x) ^ 2 ∂μ) = ∫ x, (v i x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hZsq : (∫ x, (Z x) ^ 2 ∂μ) = ∫ x, (z x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ] with x hx using congrArg (fun t : ℝ => t ^ 2) hx
  have hVV (i j : ι) : (∫ x, V i x * V j x ∂μ) = ∫ x, v i x * v j x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hV j] with x hi hj
    rw [hi, hj]
  have hVZ (i : ι) : (∫ x, V i x * Z x ∂μ) = ∫ x, v i x * z x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hV i, hZ] with x hi hz'
    rw [hi, hz']
  have h := integral_average_sub_sq_le s hs V Z hε
    (by simpa only [hVsq] using hdiag)
    (by simpa only [hVV, hZsq] using hoff)
    (by simpa only [hVZ, hZsq] using hcross)
  have hall : ∀ᵐ x ∂μ, ∀ i ∈ s, V i x = v i x :=
    (Finset.eventually_all s).2 (fun i _ => hV i)
  have heq : (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, V i x) - Z x) ^ 2) =ᵐ[μ]
      (fun x => ((s.card : ℝ)⁻¹ * (∑ i ∈ s, v i x) - z x) ^ 2) := by
    filter_upwards [hall, hZ] with x hx hz'
    rw [Finset.sum_congr rfl hx, hz']
  rwa [integral_congr_ae heq] at h

end InvariantRotation.SamplingMomentBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace InvariantRotation.SamplingMomentBounds

theorem memLp_coordinate_prod {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] (f : (i : κ) → Ω i → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (fun x => ∏ i, f i (x i)) 2 (Measure.pi μ) := by
  have hm : AEStronglyMeasurable (fun x => ∏ i, f i (x i)) (Measure.pi μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (hf i).aestronglyMeasurable.comp_measurePreserving (measurePreserving_eval μ i)
  apply (memLp_two_iff_integrable_sq hm).2
  simpa only [Finset.prod_pow] using
    Integrable.fintype_prod_dep (fun i => (hf i).integrable_sq)

theorem integral_coordinate_prod_mul {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) =
      ∏ i, ∫ x, f i x * g i x ∂μ i := by
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i x => f i x * g i x)

theorem integral_coordinate_prod_sq {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (f i x) ^ 2 ∂μ i := by
  simpa only [pow_two] using integral_coordinate_prod_mul f f (μ := μ)

theorem coordinate_product_pair_error_le
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f g z : (i : κ) → Ω i → ℝ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (herror : ∀ i, |(∫ x, f i x * g i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    |(∫ x, (∏ i, f i (x i)) * (∏ i, g i (x i)) ∂Measure.pi μ) -
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ)| ≤
      (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1) := by
  rw [integral_coordinate_prod_mul, integral_coordinate_prod_sq]
  let A : κ → ℝ := fun i => ∫ x, (z i x) ^ 2 ∂μ i
  have he := product_perturbation_bound (Finset.univ : Finset κ) A
    (fun i => (∫ x, f i x * g i x ∂μ i) - A i) hB hε
    (fun i _ => integral_nonneg (fun _ => sq_nonneg _)) (fun i _ => hbase i)
    (fun i _ => herror i)
  simpa only [add_sub_cancel, Finset.card_univ] using he

theorem coordinate_product_sq_le_pow
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : κ) → Ω i → ℝ)
    {D : ℝ} (h : ∀ i, (∫ x, (f i x) ^ 2 ∂μ i) ≤ D) :
    (∫ x, (∏ i, f i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ := by
  rw [integral_coordinate_prod_sq]
  calc
    (∏ i, ∫ x, (f i x) ^ 2 ∂μ i) ≤ ∏ _i : κ, D :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
        (fun index _ => h index)
    _ = D ^ Fintype.card κ := by simp

theorem integral_average_coordinate_products_sub_sq_le
    {κ ι : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → (i : κ) → Ω i → ℝ) (z : (i : κ) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i))
    {B D ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ B)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ x, (v n i x) ^ 2 ∂μ i) ≤ D)
    (hoff : ∀ n ∈ s, ∀ m ∈ s, n ≠ m → ∀ i,
      |(∫ x, v n i x * v m i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε)
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ x, v n i x * z i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤ ε) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
        ∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) ≤
      D ^ Fintype.card κ / (s.card : ℝ) +
        3 * ((Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)) := by
  let E : ℝ := (Fintype.card κ : ℝ) * ε * (B + ε) ^ (Fintype.card κ - 1)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hd (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, v n i (x i)) ^ 2 ∂Measure.pi μ) ≤ D ^ Fintype.card κ :=
    coordinate_product_sq_le_pow (v n) (hdiag n hn)
  have ho (n : ι) (hn : n ∈ s) (m : ι) (hm : m ∈ s) (hnm : n ≠ m) :
      (∫ x, (∏ i, v n i (x i)) * (∏ i, v m i (x i)) ∂Measure.pi μ) ≤
        (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) + E := by
    have he := coordinate_product_pair_error_le (v n) (v m) z hB hε hbase (hoff n hn m hm hnm)
    have hu := (abs_le.mp he).2
    change _ ≤ _ + E
    linarith
  have hc (n : ι) (hn : n ∈ s) :
      (∫ x, (∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) - E ≤
        (∫ x, (∏ i, v n i (x i)) * (∏ i, z i (x i)) ∂Measure.pi μ) := by
    have he := coordinate_product_pair_error_le (v n) z z hB hε hbase (hcross n hn)
    have hl := (abs_le.mp he).1
    change _ - E ≤ _
    linarith
  exact integral_average_sub_sq_le_of_memLp (μ := Measure.pi μ) s hs
    (fun n x => ∏ i, v n i (x i)) (fun x => ∏ i, z i (x i))
    (fun n => memLp_coordinate_prod (v n) (hv n)) (memLp_coordinate_prod z hz)
    hE hd ho hc

end InvariantRotation.SamplingMomentBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingMeanSquare
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
open InvariantRotation.SamplingMomentBounds

namespace Invariant233.SamplingAsymptotics

theorem integral_coordinate_product_sub_one_sq
    {κ : Type*} [Fintype κ] {Ω : κ → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : κ) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (z : (i : κ) → Ω i → ℝ) (hz : ∀ i, MemLp (z i) 2 (μ i)) :
    (∫ x, ((∏ i, z i (x i)) - 1) ^ 2 ∂Measure.pi μ) =
      (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) -
        2 * (∏ i, ∫ x, z i x ∂μ i) + 1 := by
  let Z : ((i : κ) → Ω i) → ℝ := fun x => ∏ i, z i (x i)
  have hZ : MemLp Z 2 (Measure.pi μ) := memLp_coordinate_prod z hz
  have hZi : Integrable Z (Measure.pi μ) := hZ.integrable (by norm_num)
  have hpoly : (fun x => (Z x - 1) ^ 2) =
      (fun x => (Z x) ^ 2 - 2 * Z x + 1) := by
    funext x
    ring
  change (∫ x, (Z x - 1) ^ 2 ∂Measure.pi μ) = _
  have hdiff : Integrable (fun x => (Z x) ^ 2 - 2 * Z x) (Measure.pi μ) :=
    hZ.integrable_sq.sub (hZi.const_mul 2)
  rw [hpoly, integral_add hdiff (integrable_const 1)]
  have hsub : (∫ x, (Z x) ^ 2 - 2 * Z x ∂Measure.pi μ) =
      (∫ x, (Z x) ^ 2 ∂Measure.pi μ) - 2 * (∫ x, Z x ∂Measure.pi μ) := by
    rw [integral_sub hZ.integrable_sq (hZi.const_mul 2), integral_const_mul]
  rw [hsub]
  simp only [integral_const, smul_eq_mul]
  rw [show (∫ x, (Z x) ^ 2 ∂Measure.pi μ) =
      ∏ i, ∫ x, (z i x) ^ 2 ∂μ i from integral_coordinate_prod_sq z]
  rw [show (∫ x, Z x ∂Measure.pi μ) =
      ∏ i, ∫ x, z i x ∂μ i from integral_fintype_prod_eq_prod z]
  simp

theorem integral_ideal_product_sub_one_sq_le
    (m : ℕ) {Ω : Fin m → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : (i : Fin m) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    (z : (i : Fin m) → Ω i → ℝ) (hz : ∀ i, MemLp (z i) 2 (μ i))
    (hmean : ∀ i, (∫ x, z i x ∂μ i) = kernelMass m)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ momentBase m) :
    (∫ x, ((∏ i, z i (x i)) - 1) ^ 2 ∂Measure.pi μ) ≤ idealError m := by
  rw [integral_coordinate_product_sub_one_sq z hz]
  have hprod : (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) ≤ (momentBase m) ^ m := by
    calc
      (∏ i, ∫ x, (z i x) ^ 2 ∂μ i) ≤ ∏ _i : Fin m, momentBase m :=
        Finset.prod_le_prod (fun i _ => integral_nonneg (fun x => sq_nonneg _))
          (fun i _ => hbase i)
      _ = (momentBase m) ^ m := by simp
  simp only [hmean, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  dsimp [idealError]
  linarith

theorem integral_sub_one_sq_le_split {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (v z : Ω → ℝ)
    (hv : MemLp v 2 μ) (hz : MemLp z 2 μ) :
    (∫ x, (v x - 1) ^ 2 ∂μ) ≤
      2 * (∫ x, (v x - z x) ^ 2 ∂μ) + 2 * (∫ x, (z x - 1) ^ 2 ∂μ) := by
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const 1
  have hleft : Integrable (fun x => (v x - 1) ^ 2) μ := (hv.sub h1).integrable_sq
  have hvz : Integrable (fun x => (v x - z x) ^ 2) μ := (hv.sub hz).integrable_sq
  have hz1 : Integrable (fun x => (z x - 1) ^ 2) μ := (hz.sub h1).integrable_sq
  calc
    (∫ x, (v x - 1) ^ 2 ∂μ) ≤
        ∫ x, 2 * (v x - z x) ^ 2 + 2 * (z x - 1) ^ 2 ∂μ := by
      apply integral_mono hleft ((hvz.const_mul 2).add (hz1.const_mul 2))
      intro x
      change (v x - 1) ^ 2 ≤ 2 * (v x - z x) ^ 2 + 2 * (z x - 1) ^ 2
      nlinarith [sq_nonneg (v x - 2 * z x + 1)]
    _ = _ := by rw [integral_add (hvz.const_mul 2) (hz1.const_mul 2),
      integral_const_mul, integral_const_mul]

theorem integral_sample_mean_square_le
    (m : ℕ) (hm : 1 ≤ m) {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {Ω : Fin m → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : Fin m) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (v : ι → (i : Fin m) → Ω i → ℝ) (z : (i : Fin m) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) (hz : ∀ i, MemLp (z i) 2 (μ i))
    (C : ℝ) (hC : 0 ≤ C)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ))
    (hmean : ∀ i, (∫ x, z i x ∂μ i) = kernelMass m)
    (hbase : ∀ i, (∫ x, (z i x) ^ 2 ∂μ i) ≤ momentBase m)
    (hdiag : ∀ n ∈ s, ∀ i, (∫ x, (v n i x) ^ 2 ∂μ i) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m)
    (hoff : ∀ n ∈ s, ∀ n' ∈ s, n ≠ n' → ∀ i,
      |(∫ x, v n i x * v n' i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤
        C * (m : ℝ) ^ (-(50 : ℝ)))
    (hcross : ∀ n ∈ s, ∀ i,
      |(∫ x, v n i x * z i x ∂μ i) - (∫ x, (z i x) ^ 2 ∂μ i)| ≤
        C * (m : ℝ) ^ (-(50 : ℝ))) :
    (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2
      ∂Measure.pi μ) ≤ meanSquareBound C m := by
  have hB : 0 ≤ momentBase m := by unfold momentBase; positivity
  have hε : 0 ≤ C * (m : ℝ) ^ (-(50 : ℝ)) := by positivity
  have hb := integral_average_coordinate_products_sub_sq_le s hs v z hv hz
    hB hε hbase hdiag hoff hcross
  simp only [Fintype.card_fin] at hb
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m) ^ m / (s.card : ℝ) ≤
      diagonalError m := by
    apply div_le_div_of_nonneg_left
    · exact pow_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hmreal)) m
    · exact Real.rpow_pos_of_pos hmpos _
    · exact hcard
  have hb' : (∫ x, ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) -
      ∏ i, z i (x i)) ^ 2 ∂Measure.pi μ) ≤ diagonalError m + 3 * productError C m := by
    dsimp [productError]
    linarith
  have hi := integral_ideal_product_sub_one_sq_le m z hz hmean hbase
  have hvprod (n : ι) : MemLp (fun x => ∏ i, v n i (x i)) 2 (Measure.pi μ) :=
    memLp_coordinate_prod (v n) (hv n)
  have hva : MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)))
      2 (Measure.pi μ) :=
    (memLp_finsetSum s (fun n _ => hvprod n)).const_mul _
  have hsplit := integral_sub_one_sq_le_split _ _ hva (memLp_coordinate_prod z hz)
  exact hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hb' (by norm_num))
    (mul_le_mul_of_nonneg_left hi (by norm_num)))

theorem lintegral_sample_mean_square_eq_ofReal
    (m : ℕ) {ι : Type*} (s : Finset ι)
    {Ω : Fin m → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : Fin m) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (v : ι → (i : Fin m) → Ω i → ℝ)
    (hv : ∀ n i, MemLp (v n i) 2 (μ i)) :
    (∫⁻ x, ENNReal.ofReal
      (((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2) ∂Measure.pi μ) =
      ENNReal.ofReal (∫ x,
        ((s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)) - 1) ^ 2 ∂Measure.pi μ) := by
  have hvprod (n : ι) : MemLp (fun x => ∏ i, v n i (x i)) 2 (Measure.pi μ) :=
    memLp_coordinate_prod (v n) (hv n)
  have hva : MemLp (fun x => (s.card : ℝ)⁻¹ * (∑ n ∈ s, ∏ i, v n i (x i)))
      2 (Measure.pi μ) :=
    (memLp_finsetSum s (fun n _ => hvprod n)).const_mul _
  have h1 : MemLp (fun _ : (i : Fin m) → Ω i => (1 : ℝ)) 2 (Measure.pi μ) :=
    memLp_const 1
  exact (ofReal_integral_eq_lintegral_ofReal (hva.sub h1).integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)).symm

end Invariant233.SamplingAsymptotics

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingMomentConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem manuscript_kernel_abs_le {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s v : ℝ) :
    |u s v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
  have hfirst (z : ℝ) : |manuscriptKernel m z v| ≤ (m : ℝ)^(13 / 5 : ℝ) := by
    have hn : 0 ≤ manuscriptKernel m z v :=
      rawKernel_nonneg (manuscript_parameters hm).1.le
        ⟨Int.fract_nonneg z, (Int.fract_lt_one z).le⟩
    rw [abs_of_nonneg hn]
    exact manuscriptKernel_le_height hm z v
  rcases hu with rfl | rfl
  · exact hfirst s
  · exact hfirst (s - v)

theorem manuscript_kernel_nonneg {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) (s v : ℝ) :
    0 ≤ u s v := by
  rcases hu with rfl | rfl <;>
    exact rawKernel_nonneg (manuscript_parameters hm).1.le
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem manuscript_kernel_measurable {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (Function.uncurry u) := by
  rcases hu with rfl | rfl
  · exact measurable_circleKernel _ _
  · exact measurable_circleEndpoint_pair _ _

theorem manuscript_kernel_intervalIntegrable {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) : IntervalIntegrable (u s) volume 0 1 := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound
    (by rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
    ((manuscript_kernel_measurable hu).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    ((m : ℝ)^(13 / 5 : ℝ))
  exact Filter.Eventually.of_forall fun v => by
    change ‖u s v‖ ≤ _
    simpa only [Real.norm_eq_abs] using manuscript_kernel_abs_le hm hu s v

theorem manuscript_kernel_square_intervalIntegrable {m : ℕ} (hm : 200 ≤ m)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) : IntervalIntegrable (fun v => (u s v)^2) volume 0 1 := by
  apply intervalIntegrable_square_of_bound
    (manuscript_kernel_intervalIntegrable hm hu s).def'.aestronglyMeasurable
    (by positivity : 0 ≤ (m : ℝ)^(13 / 5 : ℝ))
  intro v _
  exact manuscript_kernel_abs_le hm hu s v

theorem one_power_kernel_cross_error {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (hN : 0 < N₀) (hn : 0 < n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    |(∫ x, u s (Int.fract (n * x)) * (∫ v in (0 : ℝ)..1, u s v)
        ∂UniformIntervalPhase.lambdaLaw N₀) - (∫ v in (0 : ℝ)..1, u s v)^2| ≤
      4 * (N₀ / n) := by
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn
    (manuscript_kernel_intervalIntegrable hm hu s)
  rw [← UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN] at h
  have habs : (fun v => |u s v|) = u s :=
    funext fun v => abs_of_nonneg (manuscript_kernel_nonneg hm hu s v)
  rw [habs] at h
  obtain ⟨hb0, hb2⟩ := (both_kernel_estimates hm hu).average_bounds s
  let b := ∫ v in (0 : ℝ)..1, u s v
  change |(∫ x, u s (Int.fract (n * x)) * b ∂UniformIntervalPhase.lambdaLaw N₀) - b^2| ≤ _
  rw [integral_mul_const]
  have heq (a : ℝ) : a * b - b^2 = (a - b) * b := by ring
  rw [heq, abs_mul, abs_of_nonneg hb0]
  calc
    _ ≤ ((N₀ / n) * b) * b := mul_le_mul_of_nonneg_right h hb0
    _ = (N₀ / n) * b^2 := by ring
    _ ≤ (N₀ / n) * 4 := mul_le_mul_of_nonneg_left (by dsimp [b] <;> nlinarith) (by positivity)
    _ = _ := by ring

theorem one_power_kernel_square_le {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (hN : 0 < N₀) (hn : N₀ ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (s : ℝ) :
    (∫ x, (u s (Int.fract (n * x)))^2 ∂UniformIntervalPhase.lambdaLaw N₀) ≤
      2 * ∫ v in (0 : ℝ)..1, (u s v)^2 := by
  have hn0 := hN.trans_le hn
  have h := PeriodicIntervalDiscrepancy.uniform_angle_test_le hN hn0
    (manuscript_kernel_square_intervalIntegrable hm hu s)
  rw [← UniformIntervalPhase.lambdaLaw_eq_cond N₀ hN] at h
  simp only [abs_sq] at h
  have hr : N₀ / n ≤ 1 := (div_le_one hn0).mpr hn
  have hb : 0 ≤ ∫ v in (0 : ℝ)..1, (u s v)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  have hh := (abs_le.mp h).2
  nlinarith [mul_le_mul_of_nonneg_right hr hb]

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingNumerics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ScalarSampling

theorem eight_mul_pow_fiftytwo_le_horizon {m : ℕ} (hm : 200 ≤ m) :
    8 * (m : ℝ)^52 ≤ samplingHorizon m := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    8 * (m : ℝ)^52 ≤ (m : ℝ) * (m : ℝ)^52 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (m : ℝ)^53 := by ring
    _ = (m : ℝ)^(53 : ℝ) := (Real.rpow_natCast _ 53).symm
    _ ≤ samplingHorizon m :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem cross_error_scale {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (_hN : 0 < N₀) (hNm : N₀ ≤ (m : ℝ)^2)
    (hn : samplingHorizon m / 2 ≤ n) :
    4 * (N₀ / n) ≤ (m : ℝ)^(-(50 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQ : 0 < samplingHorizon m := Real.rpow_pos_of_pos hm0 _
  have hn0 : 0 < n := (half_pos hQ).trans_le hn
  have hprod : (4 * N₀) * (m : ℝ)^50 ≤ n := by
    calc
      (4 * N₀) * (m : ℝ)^50 ≤ (4 * (m : ℝ)^2) * (m : ℝ)^50 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNm (by norm_num)) (by positivity)
      _ = 4 * (m : ℝ)^52 := by ring
      _ ≤ samplingHorizon m / 2 := by linarith [eight_mul_pow_fiftytwo_le_horizon hm]
      _ ≤ n := hn
  have hdiv : (4 * N₀) / n ≤ 1 / (m : ℝ)^50 :=
    (div_le_div_iff₀ hn0 (pow_pos hm0 50)).mpr (by simpa using hprod)
  simpa [Real.rpow_neg hm0.le, Real.rpow_ofNat, div_eq_mul_inv, mul_assoc] using hdiv

end Invariant233.ScalarSampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ScalarSamplingPairMoments
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma scalarPairLaw_probability {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (scalarPairLaw N) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  dsimp [scalarPairLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_scalarUnitLaw (f : ℝ → ℝ) :
    (∫ s, f s ∂scalarUnitLaw) = ∫ s in (0 : ℝ)..1, f s := by
  simp only [scalarUnitLaw, restrict_Ico_eq_restrict_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma measurable_kernel_mean {m : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Measurable (fun s => ∫ v in (0 : ℝ)..1, u s v) := by
  simpa only [Function.uncurry, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    ((manuscript_kernel_measurable hu).stronglyMeasurable.integral_prod_right').measurable

lemma integrable_kernel_mean_square {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun s => (∫ v in (0 : ℝ)..1, u s v)^2) scalarUnitLaw := by
  apply Integrable.of_bound ((measurable_kernel_mean hu).pow_const 2).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro s
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith

lemma integrable_sampled_product {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (n n' : ℝ) :
    Integrable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1)) *
      u p.2 (Int.fract (n' * p.1))) (scalarPairLaw N) := by
  let := scalarPairLaw_probability hN
  have hmeas (k : ℝ) : Measurable (fun p : ℝ × ℝ => u p.2 (Int.fract (k * p.1))) :=
    (manuscript_kernel_measurable hu).comp
      (measurable_snd.prodMk (measurable_fract.comp (measurable_const.mul measurable_fst)))
  apply Integrable.of_bound ((hmeas n).mul (hmeas n')).aestronglyMeasurable
    (((m : ℝ)^(13 / 5 : ℝ))^2)
  apply Filter.Eventually.of_forall
  intro p
  change |u p.2 (Int.fract (n * p.1)) * u p.2 (Int.fract (n' * p.1))| ≤ _
  rw [abs_mul, pow_two]
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.2 _) (manuscript_kernel_abs_le hm hu p.2 _)
    (abs_nonneg _) (by positivity)

lemma integrable_sampled_cross {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m)
    (n : ℝ) :
    Integrable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1)) *
      (∫ v in (0 : ℝ)..1, u p.2 v)) (scalarPairLaw N) := by
  let := scalarPairLaw_probability hN
  have hmeas : Measurable (fun p : ℝ × ℝ => u p.2 (Int.fract (n * p.1))) :=
    (manuscript_kernel_measurable hu).comp
      (measurable_snd.prodMk (measurable_fract.comp (measurable_const.mul measurable_fst)))
  apply Integrable.of_bound
    (hmeas.mul ((measurable_kernel_mean hu).comp measurable_snd)).aestronglyMeasurable
    ((m : ℝ)^(13 / 5 : ℝ) * 2)
  apply Filter.Eventually.of_forall
  intro p
  change |u p.2 (Int.fract (n * p.1)) * (∫ v in (0 : ℝ)..1, u p.2 v)| ≤ _
  rw [abs_mul]
  obtain ⟨h0, h2⟩ := (both_kernel_estimates hm hu).average_bounds p.2
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.2 _)
    (by simpa only [abs_of_nonneg h0] using h2) (abs_nonneg _) (by positivity)

lemma scalarPair_error_transfer {N ε : ℝ} (hN : 0 < N)
    {f : ℝ × ℝ → ℝ} {g : ℝ → ℝ}
    (hf : Integrable f (scalarPairLaw N)) (hg : Integrable g scalarUnitLaw)
    (h : ∀ s, |(∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s| ≤ ε) :
    |(∫ p, f p ∂scalarPairLaw N) - ∫ s, g s ∂scalarUnitLaw| ≤ ε := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  change Integrable f ((UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw) at hf
  rw [scalarPairLaw, integral_prod_symm f hf, ← integral_sub hf.integral_prod_right hg]
  have hh := norm_integral_le_of_norm_le_const
    (μ := scalarUnitLaw) (f := fun s => (∫ x, f (x, s) ∂UniformIntervalPhase.lambdaLaw N) - g s)
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using h s)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

theorem scalarPair_cross_error {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hNm : N ≤ (m : ℝ)^2) (hn : samplingHorizon m / 2 ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    |(∫ p, u p.2 (Int.fract (n * p.1)) * (∫ v in (0 : ℝ)..1, u p.2 v)
        ∂scalarPairLaw N) - (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2)| ≤
      (m : ℝ)^(-(50 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : 0 < n := (half_pos (Real.rpow_pos_of_pos hm0 _)).trans_le hn
  rw [← integral_scalarUnitLaw]
  apply scalarPair_error_transfer hN (integrable_sampled_cross hm hN hu n)
    (integrable_kernel_mean_square hm hu)
  intro s
  exact (one_power_kernel_cross_error hm hN hn0 hu s).trans (cross_error_scale hm hN hNm hn)

lemma integrable_haar_kernel_square {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    Integrable (fun p : ℝ × ℝ => (u p.1 p.2)^2) (scalarUnitLaw.prod scalarUnitLaw) := by
  apply Integrable.of_bound ((manuscript_kernel_measurable hu).pow_const 2).aestronglyMeasurable
    (((m : ℝ)^(13 / 5 : ℝ))^2)
  apply Filter.Eventually.of_forall
  intro p
  change |(u p.1 p.2)^2| ≤ _
  rw [abs_pow, pow_two, pow_two]
  exact mul_le_mul (manuscript_kernel_abs_le hm hu p.1 p.2)
    (manuscript_kernel_abs_le hm hu p.1 p.2) (abs_nonneg _) (by positivity)

theorem scalarPair_diagonal_le {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hn : N ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    (∫ p, (u p.2 (Int.fract (n * p.1)))^2 ∂scalarPairLaw N) ≤
      2 * (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, (u s v)^2) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  have hf : Integrable (fun p : ℝ × ℝ => (u p.2 (Int.fract (n * p.1)))^2)
      ((UniformIntervalPhase.lambdaLaw N).prod scalarUnitLaw) := by
    simpa only [pow_two, scalarPairLaw] using integrable_sampled_product hm hN hu n n
  have hg : Integrable (fun s => ∫ v in (0 : ℝ)..1, (u s v)^2) scalarUnitLaw := by
    simpa only [integral_scalarUnitLaw] using (integrable_haar_kernel_square hm hu).integral_prod_left
  rw [scalarPairLaw, integral_prod_symm _ hf]
  calc
    _ ≤ ∫ s, 2 * (∫ v in (0 : ℝ)..1, (u s v)^2) ∂scalarUnitLaw :=
      integral_mono hf.integral_prod_right (hg.const_mul 2)
        (fun s => one_power_kernel_square_le hm hN hn hu s)
    _ = _ := by rw [integral_const_mul, integral_scalarUnitLaw]

theorem scalarPair_diagonal_rate {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hN : 0 < N) (hn : N ≤ n)
    {u : ℝ → ℝ → ℝ} (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    (∫ p, (u p.2 (Int.fract (n * p.1)))^2 ∂scalarPairLaw N) ≤
       8 * (m : ℝ)^(3 / 5 : ℝ) * Real.log m :=
  (scalarPair_diagonal_le hm hN hn hu).trans
    ((both_kernel_estimates hm hu).twice_square_mass_rate hm)

end Invariant233.ScalarSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingSelection
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

lemma phaseLaw_eq_pi (m : ℕ) {N : ℝ} (hN : 0 < N) :
    phaseLaw m N = Measure.pi (fun _ : Fin m =>
      ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) := by
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  exact Measure.infinitePi_eq_pi _

lemma measurable_kernel_pair (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => CircleParameterData.kernel m p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => CircleParameterData.delta p.1) :=
    measurable_fst.fract.min (measurable_const.sub measurable_fst.fract)
  unfold CircleParameterData.kernel
  apply Measurable.ite
  · exact (measurableSet_le measurable_const hd).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul hd)))
  · exact measurable_const.div (measurable_const.mul hd)
  · exact measurable_const

lemma measurable_orientedKernel_pair (m : ℕ) (endpoint : Bool) :
    Measurable (fun p : ℝ × ℝ =>
      CircleParameterData.orientedKernel endpoint m p.1 p.2) := by
  cases endpoint
  · exact measurable_kernel_pair m
  · exact (measurable_kernel_pair m).comp
      ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma measurable_average_pair (m : ℕ) (samples : Finset ℕ) (endpoint : Bool) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      average m samples endpoint p.1 p.2) := by
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  have hz : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      CircleParameterData.rep (p.2 i)) :=
    CircleParameterData.measurable_rep.comp
      ((show Measurable (fun z : Fin m → Circle => z i) from measurable_pi_apply i).comp
        measurable_snd)
  have hv : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      Int.fract ((n : ℝ) * p.1 i)) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract
  exact (measurable_orientedKernel_pair m endpoint).comp (hz.prodMk hv)

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.average_eq_trialAverage _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

lemma pairLaw_probability {N : ℝ} (hN : 0 < N) : IsProbabilityMeasure (pairLaw N) := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  dsimp [pairLaw]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma measurable_coordinateSample (m : ℕ) (endpoint : Bool) (n : ℕ) :
    Measurable (coordinateSample m endpoint n) := by
  exact (measurable_orientedKernel_pair m endpoint).comp
    ((CircleParameterData.measurable_rep.comp measurable_snd).prodMk
      (measurable_const.mul measurable_fst).fract)

theorem pairLaw_representative_measurePreserving {N : ℝ} (_hN : 0 < N) :
    MeasurePreserving (fun p : ℝ × Circle => (p.1, CircleParameterData.rep p.2))
      (pairLaw N)
      ((ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
  let ν : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure ν :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) _hN)
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  exact (MeasurePreserving.id ν).prod CocycleSupport.measurePreserving_circleRepresentative

theorem integral_pairLaw_representative {N : ℝ} (hN : 0 < N) (f : ℝ × ℝ → ℝ) :
    (∫ p, f (p.1, CircleParameterData.rep p.2) ∂pairLaw N) =
      ∫ p, f p ∂(ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  have hr : MeasurableEmbedding (CircleParameterData.rep : Circle → ℝ) := by
    exact (MeasurableEmbedding.subtype_coe measurableSet_Ico).comp
      (AddCircle.measurableEquivIco (1 : ℝ) 0).measurableEmbedding
  exact (pairLaw_representative_measurePreserving hN).integral_comp
    (MeasurableEmbedding.id.prodMap hr) f

theorem expectation_squaredError_eq_pair_integral
    (m : ℕ) {N : ℝ} (hN : 0 < N) (samples : Finset ℕ) (endpoint : Bool) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) =
      ∫⁻ x : Fin m → ℝ × Circle, ENNReal.ofReal
        (((samples.card : ℝ)⁻¹ * (∑ n ∈ samples,
          ∏ i : Fin m, coordinateSample m endpoint n (x i)) - 1) ^ 2)
          ∂Measure.pi (fun _ : Fin m => pairLaw N) := by
  let ν : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure ν :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  let F : (Fin m → ℝ) × (Fin m → Circle) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((average m samples endpoint p.1 p.2 - 1) ^ 2)
  have hF : Measurable F :=
    (((measurable_average_pair m samples endpoint).sub_const 1).pow_const 2).ennreal_ofReal
  have he := measurePreserving_arrowProdEquivProdArrow ℝ Circle (Fin m)
    (fun _ => ν) (fun _ => circleMeasure)
  have hi := he.lintegral_comp hF
  rw [lintegral_prod F hF.aemeasurable] at hi
  simpa only [phaseLaw_eq_pi m hN, squaredError, spatialLaw, pairLaw,
    F, average, coordinateSample, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, ν] using hi.symm

theorem memLp_coordinateSample {m : ℕ} (hm : 0 < m) {N : ℝ} (hN : 0 < N)
    (endpoint : Bool) (n : ℕ) :
    MemLp (coordinateSample m endpoint n) 2 (pairLaw N) := by
  let := pairLaw_probability hN
  apply MemLp.of_bound (measurable_coordinateSample m endpoint n).aestronglyMeasurable
    ((m : ℝ) ^ 2 / CircleParameterData.kernelWidth m)
  apply Eventually.of_forall
  intro p
  have h := CircleParameterData.orientedKernel_bounds endpoint hm
    (CircleParameterData.rep p.2) (Int.fract ((n : ℝ) * p.1))
  simpa only [coordinateSample, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma measurable_coordinateIdeal (m : ℕ) (endpoint : Bool) :
    Measurable (coordinateIdeal m endpoint) := by
  have h : Measurable (fun p : (ℝ × Circle) × ℝ =>
      CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.1.2) p.2) :=
    (measurable_orientedKernel_pair m endpoint).comp
      ((CircleParameterData.measurable_rep.comp (measurable_snd.comp measurable_fst)).prodMk
        measurable_snd)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem coordinateIdeal_norm_le {m : ℕ} (hm : 0 < m) (endpoint : Bool) (p : ℝ × Circle) :
    ‖coordinateIdeal m endpoint p‖ ≤ (m : ℝ) ^ 2 / CircleParameterData.kernelWidth m := by
  have hb : ∀ᵐ v : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2) v‖ ≤
        (m : ℝ) ^ 2 / CircleParameterData.kernelWidth m := by
    apply Eventually.of_forall
    intro v
    have h := CircleParameterData.orientedKernel_bounds endpoint hm
      (CircleParameterData.rep p.2) v
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have h := norm_integral_le_of_norm_le_const hb
  simpa [coordinateIdeal, Measure.real] using h

theorem memLp_coordinateIdeal {m : ℕ} (hm : 0 < m) {N : ℝ} (hN : 0 < N)
    (endpoint : Bool) : MemLp (coordinateIdeal m endpoint) 2 (pairLaw N) := by
  let := pairLaw_probability hN
  exact MemLp.of_bound (measurable_coordinateIdeal m endpoint).aestronglyMeasurable
    ((m : ℝ) ^ 2 / CircleParameterData.kernelWidth m)
    (Eventually.of_forall (coordinateIdeal_norm_le hm endpoint))

theorem expectation_squaredError_le_meanSquareBound
    (m : ℕ) (hm : 1 ≤ m) {N : ℝ} (hN : 0 < N)
    (samples : Finset ℕ) (hs : samples.Nonempty) (endpoint : Bool)
    (C : ℝ) (hC : 0 ≤ C)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
    (hmean : (∫ p, coordinateIdeal m endpoint p ∂pairLaw N) =
      SamplingAsymptotics.kernelMass m)
    (hbase : (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N) ≤
      SamplingAsymptotics.momentBase m)
    (hdiag : ∀ n ∈ samples, (∫ p, (coordinateSample m endpoint n p) ^ 2 ∂pairLaw N) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m)
    (hoff : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
      |(∫ p, coordinateSample m endpoint n p * coordinateSample m endpoint n' p ∂pairLaw N) -
        (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤ C * (m : ℝ) ^ (-(50 : ℝ)))
    (hcross : ∀ n ∈ samples,
      |(∫ p, coordinateSample m endpoint n p * coordinateIdeal m endpoint p ∂pairLaw N) -
        (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤ C * (m : ℝ) ^ (-(50 : ℝ))) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound C m) := by
  let := pairLaw_probability hN
  have hmpos : 0 < m := by omega
  rw [expectation_squaredError_eq_pair_integral m hN samples endpoint]
  rw [SamplingAsymptotics.lintegral_sample_mean_square_eq_ofReal m samples
    (fun n (_ : Fin m) => coordinateSample m endpoint n)
    (fun n _ => memLp_coordinateSample hmpos hN endpoint n)]
  apply ENNReal.ofReal_le_ofReal
  exact SamplingAsymptotics.integral_sample_mean_square_le m hm samples hs
    (fun n (_ : Fin m) => coordinateSample m endpoint n)
    (fun _ : Fin m => coordinateIdeal m endpoint)
    (fun n _ => memLp_coordinateSample hmpos hN endpoint n)
    (fun _ => memLp_coordinateIdeal hmpos hN endpoint)
    C hC hcard (fun _ => hmean) (fun _ => hbase)
    (fun n hn _ => hdiag n hn) (fun n hn n' hn' hne _ => hoff n hn n' hn' hne)
    (fun n hn _ => hcross n hn)

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingScalar
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.TrialSampling

theorem coordinateSample_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (n : ℕ) (p : ℝ × Circle) :
    coordinateSample m endpoint n p =
      if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1))
      else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2)
        (Int.fract ((n : ℝ) * p.1)) := by
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

theorem coordinateIdeal_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) (p : ℝ × Circle) :
    coordinateIdeal m endpoint p =
      ∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m (CircleParameterData.rep p.2) v
        else ScalarSampling.manuscriptKernel m (CircleParameterData.rep p.2) v := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  exact ScalarSampling.parameter_orientedKernel_eq hm endpoint _ ⟨hv.1.le, hv.2⟩

theorem integral_coordinate_moment_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool)
    (F : (ℕ → ℝ) → ℝ → ℝ) :
    (∫ p, F (fun n => coordinateSample m endpoint n p) (coordinateIdeal m endpoint p)
      ∂pairLaw N) =
      ∫ p : ℝ × ℝ,
        F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
            (Int.fract ((n : ℝ) * p.1))
          else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
          (∫ v in (0 : ℝ)..1,
            if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
            else ScalarSampling.manuscriptKernel m p.2 v)
        ∂(UniformIntervalPhase.lambdaLaw N).prod
          (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  simp_rw [coordinateSample_eq_scalar hm, coordinateIdeal_eq_scalar hm]
  rw [UniformIntervalPhase.lambdaLaw_eq_cond N hN]
  exact integral_pairLaw_representative hN (fun p =>
    F (fun n => if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2
          (Int.fract ((n : ℝ) * p.1))
        else ScalarSampling.manuscriptKernel m p.2 (Int.fract ((n : ℝ) * p.1)))
      (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m p.2 v
        else ScalarSampling.manuscriptKernel m p.2 v))

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingIdealMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.TrialSampling

private theorem scalar_orientation_estimates {m : ℕ} (hm : 200 ≤ m)
    (endpoint : Bool) : ScalarSampling.KernelEstimates m (fun z v =>
      if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) := by
  cases endpoint
  · exact ScalarSampling.manuscriptKernel_estimates hm
  · exact ScalarSampling.manuscriptEndpointKernel_estimates hm

theorem integral_coordinateIdeal_comp_eq_scalar {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) (f : ℝ → ℝ) :
    (∫ p, f (coordinateIdeal m endpoint p) ∂pairLaw N) =
      ∫ z in (0 : ℝ)..1, f (∫ v in (0 : ℝ)..1,
        if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
        else ScalarSampling.manuscriptKernel m z v) := by
  let := UniformIntervalPhase.lambdaLaw_probability N hN
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun _ a => f a)]
  rw [integral_fun_snd (fun z : ℝ => f (∫ v in (0 : ℝ)..1,
    if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
    else ScalarSampling.manuscriptKernel m z v))]
  simp only [probReal_univ, one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Ico_eq_integral_Ioc

theorem integral_coordinateIdeal_eq_kernelMass {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, coordinateIdeal m endpoint p ∂pairLaw N) =
      SamplingAsymptotics.kernelMass m := by
  rw [integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a)]
  rw [(scalar_orientation_estimates hm endpoint).mass]
  simp only [SamplingAsymptotics.kernelMass, Real.rpow_neg (Nat.cast_nonneg m),
    Real.rpow_two, div_eq_mul_inv]

theorem integral_coordinateIdeal_sq_le_momentBase {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) :
    (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N) ≤
      SamplingAsymptotics.momentBase m := by
  rw [integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a ^ 2)]
  exact ScalarSampling.KernelEstimates.average_square_source_bound hm
    (scalar_orientation_estimates hm endpoint)

end Invariant233.TrialSampling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrialSamplingActualMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.ScalarSampling.TestedSampling.firstKernel_univ_univ _root_.OAI.Invariant233.ScalarSampling.TestedSampling.secondKernel_univ_univ _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace Invariant233.TrialSampling

private theorem scalar_orientation_mem (m : ℕ) (endpoint : Bool) :
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptKernel m ∨
    (fun z v => if endpoint then ScalarSampling.manuscriptEndpointKernel m z v
      else ScalarSampling.manuscriptKernel m z v) = ScalarSampling.manuscriptEndpointKernel m := by
  cases endpoint <;> simp

theorem coordinateSample_diagonal_rate {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (endpoint : Bool) (n : ℕ) (hn : N ≤ (n : ℝ)) :
    (∫ p, (coordinateSample m endpoint n p) ^ 2 ∂pairLaw N) ≤
      8 * (m : ℝ) ^ (3 / 5 : ℝ) * Real.log m := by
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun a _ => (a n) ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_diagonal_rate hm hN hn (scalar_orientation_mem m endpoint)

theorem coordinateSample_cross_error {m : ℕ} (hm : 200 ≤ m)
    {N : ℝ} (hN : 0 < N) (hNm : N ≤ (m : ℝ) ^ 2)
    (endpoint : Bool) (n : ℕ) (hn : ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ)) :
    |(∫ p, coordinateSample m endpoint n p * coordinateIdeal m endpoint p ∂pairLaw N) -
      (∫ p, (coordinateIdeal m endpoint p) ^ 2 ∂pairLaw N)| ≤
      (m : ℝ) ^ (-(50 : ℝ)) := by
  rw [integral_coordinate_moment_eq_scalar hm hN endpoint (fun a b => a n * b),
    integral_coordinateIdeal_comp_eq_scalar hm hN endpoint (fun a => a ^ 2)]
  simpa only [ScalarSampling.scalarPairLaw, ScalarSampling.scalarUnitLaw] using
    ScalarSampling.scalarPair_cross_error hm hN hNm hn (scalar_orientation_mem m endpoint)

theorem scale_le_of_half_horizon {m : ℕ} (hm : 200 ≤ m) {N n : ℝ}
    (hNm : N ≤ (m : ℝ) ^ 2) (hn : ScalarSampling.samplingHorizon m / 2 ≤ n) :
    N ≤ n := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : 2 * (m : ℝ) ^ 2 ≤ ScalarSampling.samplingHorizon m := by
    calc
      2 * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith [sq_nonneg (m : ℝ)]
      _ = (m : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ ScalarSampling.samplingHorizon m :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith

theorem expectation_squaredError_le_actual_bound_oai
    {m : ℕ} (hm : 200 ≤ m) {N : ℝ} (hN : 0 < N)
    (hNm : N ≤ (m : ℝ) ^ 2) (samples : Finset ℕ) (hs : samples.Nonempty)
    (hcard : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (samples.card : ℝ))
    (hrange : ∀ n ∈ samples, ScalarSampling.samplingHorizon m / 2 ≤ (n : ℝ))
    (hpair : ∀ n ∈ samples, ∀ n' ∈ samples, n ≠ n' →
      ScalarSampling.SamplingPair m N N n n') (endpoint : Bool) :
    (∫⁻ phase, squaredError m samples endpoint phase ∂phaseLaw m N) ≤
      ENNReal.ofReal (SamplingAsymptotics.meanSquareBound 3509 m) := by
  apply expectation_squaredError_le_meanSquareBound m (by omega) hN samples hs endpoint
    3509 (by norm_num) hcard
  · exact integral_coordinateIdeal_eq_kernelMass hm hN endpoint
  · exact integral_coordinateIdeal_sq_le_momentBase hm hN endpoint
  · intro n hn
    exact coordinateSample_diagonal_rate hm hN endpoint n
      (scale_le_of_half_horizon hm hNm (hrange n hn))
  · intro n hn n' hn' hne
    exact coordinateSample_offdiag_error hm (hpair n hn n' hn' hne) endpoint
  · intro n hn
    apply (coordinateSample_cross_error hm hN hNm endpoint n (hrange n hn)).trans
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg m) (-(50 : ℝ))]

end Invariant233.TrialSampling

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound_oai := @OAI.Invariant233.TrialSampling.expectation_squaredError_le_actual_bound_oai
