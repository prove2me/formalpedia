-- Prove2me | solution 1 for Kyprianou.exercise2_11_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:43:22.423157+00:00
-- url     : https://prove2.me/submissions/85bd1d93-3211-4073-a9fc-5e60dab785b0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_subordinatorCriterionCh02V3

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise211Helpers

/-! ### Elementary real and complex estimates -/

private lemma norm_cexp_I_mul_mul_ofReal (z : ℂ) (x : ℝ) :
    ‖Complex.exp (Complex.I * z * (x : ℂ))‖ = Real.exp (-z.im * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

private lemma norm_cexp_I_mul_mul_ofReal_le_one {z : ℂ} {x : ℝ} (hz : 0 ≤ z.im) (hx : 0 ≤ x) :
    ‖Complex.exp (Complex.I * z * (x : ℂ))‖ ≤ 1 := by
  rw [norm_cexp_I_mul_mul_ofReal]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

private lemma norm_cexp_sub_one_le_norm {w : ℂ} (hw : w.re ≤ 0) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * w)) (w * Complex.exp ((t : ℂ) * w)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    simpa [mul_comm] using h1.cexp
  have hcont : Continuous (fun s : ℝ => w * Complex.exp ((s : ℂ) * w)) :=
    continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hftc
  rw [← hftc]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖w * Complex.exp ((t : ℂ) * w)‖ ≤ ‖w‖ := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * w).re = t * w.re := by simp [Complex.mul_re]
    rw [hre]
    have hexp : Real.exp (t * w.re) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1.le hw)
    calc ‖w‖ * Real.exp (t * w.re) ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hexp (norm_nonneg w)
      _ = ‖w‖ := mul_one _
  calc ‖∫ t in (0 : ℝ)..1, w * Complex.exp ((t : ℂ) * w)‖
      ≤ ‖w‖ * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ‖w‖ := by norm_num

private lemma norm_cexp_I_mul_mul_sub_one_le {z : ℂ} {x : ℝ} (hz : 0 ≤ z.im) (hx : 0 ≤ x) :
    ‖Complex.exp (Complex.I * z * (x : ℂ)) - 1‖ ≤ max 2 ‖z‖ * min 1 x := by
  have hre : (Complex.I * z * (x : ℂ)).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    have h1 := norm_cexp_sub_one_le_norm hre
    have h2 : ‖Complex.I * z * (x : ℂ)‖ = ‖z‖ * x := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hx]
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right 2 ‖z‖) hx)
  · push Not at hx1
    rw [min_eq_left hx1.le, mul_one]
    have h1 : ‖Complex.exp (Complex.I * z * (x : ℂ)) - 1‖ ≤
        ‖Complex.exp (Complex.I * z * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    have h2 : ‖Complex.exp (Complex.I * z * (x : ℂ))‖ ≤ 1 := norm_cexp_I_mul_mul_ofReal_le_one hz hx
    have h3 : (2 : ℝ) ≤ max 2 ‖z‖ := le_max_left 2 ‖z‖
    simp only [norm_one] at h1
    linarith

private lemma mul_exp_neg_le_inv {ε x : ℝ} (hε : 0 < ε) (_hx : 0 ≤ x) :
    x * Real.exp (-ε * x) ≤ 1 / ε := by
  have h1 : ε * x ≤ Real.exp (ε * x) := by
    have := Real.add_one_le_exp (ε * x)
    linarith
  have hexp_pos : 0 < Real.exp (ε * x) := Real.exp_pos _
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hexp_pos hε]
  nlinarith

/-! ### Measure-theoretic facts for a subordinator Lévy measure -/

private lemma sigmaFinite_of_isLevyMeasure {ν : Measure ℝ}
    (hν : ProbabilityTheory.IsLevyMeasure ν) : SigmaFinite ν := by
  refine ⟨⟨{
    set := fun n => if n = 0 then {0} else {x : ℝ | 1 / (n : ℝ) ≤ |x|}
    set_mem := fun _ => trivial
    finite := fun n => by
      by_cases hn : n = 0
      · subst hn; simp [hν.1]
      · simp only [hn, ↓reduceIte]
        have hpos : (0 : ℝ) < 1 / (n : ℝ) := by positivity
        exact hν.measure_setOf_abs_ge_lt_top hpos
    spanning := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      · have hpos : 0 < |x| := abs_pos.mpr hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        refine ⟨n + 1, ?_⟩
        simp only [Nat.succ_ne_zero, ↓reduceIte, Set.mem_ofPred_eq]
        push_cast
        exact le_of_lt hn
  }⟩⟩

private lemma restrict_Ioi_eq_self_of_subordinator {ν : Measure ℝ}
    (hν : ProbabilityTheory.IsLevyMeasure ν) (hν_neg : ν (Set.Iio (0 : ℝ)) = 0) :
    ν.restrict (Set.Ioi (0 : ℝ)) = ν := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  have hcompl : {x : ℝ | x ∉ Set.Ioi (0 : ℝ)} = Set.Iio (0 : ℝ) ∪ {0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Ioi, not_lt, Set.mem_union, Set.mem_Iio,
      Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hcompl]
  exact measure_union_null hν_neg hν.1

private lemma integrable_min_one_id_Ioi {ν : Measure ℝ}
    (hmin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi (0 : ℝ)))) :
    Integrable (fun x : ℝ => min (1 : ℝ) x) (ν.restrict (Set.Ioi (0 : ℝ))) := by
  refine hmin.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_pos hx]

private lemma integrableOn_id_Ioo_of_min {ν : Measure ℝ}
    (hmin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi (0 : ℝ)))) :
    IntegrableOn (fun x : ℝ => x) (Set.Ioo (0 : ℝ) 1) ν := by
  have h1 : IntegrableOn (fun x : ℝ => min (1 : ℝ) |x|) (Set.Ioo (0 : ℝ) 1) ν :=
    IntegrableOn.mono_set hmin Set.Ioo_subset_Ioi_self
  refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioo
  dsimp only
  rw [abs_of_pos hx.1, min_eq_right hx.2.le]

/-! ### Part (2): Tail integral identity via Tonelli -/

private lemma part_two_tail_identity
    {ν : Measure ℝ} (hν : ProbabilityTheory.IsLevyMeasure ν)
    {q : ℝ} (hq : 0 < q) :
    ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν =
      q * ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-q * x) * (ν (Set.Ioi x)).toReal ∂volume := by
  have : SigmaFinite ν := sigmaFinite_of_isLevyMeasure hν
  let μν : Measure ℝ := ν.restrict (Set.Ioi (0 : ℝ))
  let μL : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  have hftc : ∀ x : ℝ, 0 < x →
      ∫⁻ y in Set.Ioi (0 : ℝ),
        (if y < x then ENNReal.ofReal (q * Real.exp (-q * y)) else 0) ∂volume =
      ENNReal.ofReal (1 - Real.exp (-q * x)) := by
    intro x hx
    have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun s : ℝ => -Real.exp (-q * s)) (q * Real.exp (-q * y)) y := by
      intro y _
      have h1 : HasDerivAt (fun s : ℝ => -q * s) (-q) y := by
        simpa using (hasDerivAt_id y).const_mul (-q)
      have h2 := h1.exp.neg
      rw [show -(Real.exp (-q * y) * -q) = q * Real.exp (-q * y) by ring] at h2
      exact h2
    have hcont : Continuous (fun y : ℝ => q * Real.exp (-q * y)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 x)
    simp only [mul_zero, Real.exp_zero, sub_neg_eq_add] at hint
    have hint_Ioc : ∫ y in Set.Ioc (0 : ℝ) x, q * Real.exp (-q * y) ∂volume =
        1 - Real.exp (-q * x) := by
      rw [← intervalIntegral.integral_of_le hx.le, hint]; ring
    have hint_Ioo : ∫ y in Set.Ioo (0 : ℝ) x, q * Real.exp (-q * y) ∂volume =
        1 - Real.exp (-q * x) := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, hint_Ioc]
    have hnn : ∀ᵐ y ∂(volume.restrict (Set.Ioo (0 : ℝ) x)), 0 ≤ q * Real.exp (-q * y) :=
      ae_of_all _ fun y => mul_nonneg hq.le (Real.exp_nonneg _)
    have hinteg : IntegrableOn (fun y : ℝ => q * Real.exp (-q * y)) (Set.Ioo (0 : ℝ) x) volume :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hl := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinteg hnn
    rw [hint_Ioo] at hl
    rw [hl]
    have hind : (fun y : ℝ => if y < x then ENNReal.ofReal (q * Real.exp (-q * y)) else 0) =
        (Set.Iio x).indicator (fun y => ENNReal.ofReal (q * Real.exp (-q * y))) := by
      ext y; simp [Set.indicator]
    rw [hind, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hinter : Set.Iio x ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) x := by
      ext y; simp [and_comm]
    rw [hinter]
  have htonelli :
      ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-q * x)) ∂μν =
        ∫⁻ y, ENNReal.ofReal (q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal) ∂μL := by
    let F : ℝ → ℝ → ℝ≥0∞ := fun x y =>
      if y < x then ENNReal.ofReal (q * Real.exp (-q * y)) else 0
    have hF_meas : Measurable (Function.uncurry F) := by
      have hopen : IsOpen {p : ℝ × ℝ | p.2 < p.1} := isOpen_lt continuous_snd continuous_fst
      have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (q * Real.exp (-q * p.2))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_const.mul (Real.continuous_exp.measurable.comp
            (measurable_const.mul measurable_snd)))
      exact Measurable.ite hopen.measurableSet hg measurable_const
    have hlhs : ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-q * x)) ∂μν =
        ∫⁻ x, ∫⁻ y, F x y ∂μL ∂μν := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (hftc x hx).symm
    have hrhs : ∫⁻ y, ∫⁻ x, F x y ∂μν ∂μL =
        ∫⁻ y, ENNReal.ofReal (q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal) ∂μL := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hind : (fun x : ℝ => F x y) =
          (Set.Ioi y).indicator (fun _ => ENNReal.ofReal (q * Real.exp (-q * y))) := by
        ext x; simp [F, Set.indicator]
      rw [hind, lintegral_indicator measurableSet_Ioi, lintegral_const,
        Measure.restrict_apply_univ]
      have hmeas_eq : μν (Set.Ioi y) = ν (Set.Ioi y) := by
        dsimp [μν]
        rw [Measure.restrict_apply measurableSet_Ioi,
          Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hy.le)]
      rw [hmeas_eq]
      have hlt : ν (Set.Ioi y) < ⊤ := by
        have hsub : Set.Ioi y ⊆ {z : ℝ | y ≤ |z|} := fun z hz => by
          have hzpos : 0 < z := lt_trans hy hz
          rw [Set.mem_ofPred_eq, abs_of_pos hzpos]
          exact le_of_lt hz
        exact lt_of_le_of_lt (measure_mono hsub) (hν.measure_setOf_abs_ge_lt_top hy)
      rw [ENNReal.ofReal_mul (mul_nonneg hq.le (Real.exp_nonneg _)), ENNReal.ofReal_toReal hlt.ne]
    rw [hlhs, lintegral_lintegral_swap hF_meas.aemeasurable, hrhs]
  have h1_nn : (0 : ℝ → ℝ) ≤ᵐ[μν] fun x => 1 - Real.exp (-q * x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := hx
    change 0 ≤ 1 - Real.exp (-q * x)
    have : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have h1_meas : AEStronglyMeasurable (fun x : ℝ => 1 - Real.exp (-q * x)) μν :=
    (continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  have htail_anti : Antitone (fun y : ℝ => ν (Set.Ioi y)) :=
    fun _ _ h => measure_mono (Set.Ioi_subset_Ioi h)
  have htail_meas : Measurable (fun y : ℝ => (ν (Set.Ioi y)).toReal) :=
    ENNReal.measurable_toReal.comp htail_anti.measurable
  have h2_meas : AEStronglyMeasurable
      (fun y : ℝ => q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal) μL :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).measurable.mul
      htail_meas).aestronglyMeasurable
  have h2_nn : (0 : ℝ → ℝ) ≤ᵐ[μL] fun y => q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal :=
    ae_of_all _ fun y => mul_nonneg (mul_nonneg hq.le (Real.exp_nonneg _)) ENNReal.toReal_nonneg
  calc ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν
      = (∫⁻ x, ENNReal.ofReal (1 - Real.exp (-q * x)) ∂μν).toReal :=
        integral_eq_lintegral_of_nonneg_ae h1_nn h1_meas
    _ = (∫⁻ y, ENNReal.ofReal (q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal) ∂μL).toReal := by
        rw [htonelli]
    _ = ∫ y, q * Real.exp (-q * y) * (ν (Set.Ioi y)).toReal ∂μL :=
        (integral_eq_lintegral_of_nonneg_ae h2_nn h2_meas).symm
    _ = ∫ y, q * (Real.exp (-q * y) * (ν (Set.Ioi y)).toReal) ∂μL := by
        congr 1; ext y; ring
    _ = q * ∫ y in Set.Ioi (0 : ℝ), Real.exp (-q * y) * (ν (Set.Ioi y)).toReal ∂volume :=
        integral_const_mul q _

/-! ### Part (3): Drift recovery via dominated convergence -/

private lemma part_three_drift_recovery
    {ν : Measure ℝ}
    (hmin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi (0 : ℝ))))
    (d : ℝ) :
    Tendsto (fun q : ℝ =>
        (d * q + ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν) / q)
      atTop (nhds d) := by
  have hmin_x : Integrable (fun x : ℝ => min (1 : ℝ) x) (ν.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_min_one_id_Ioi hmin
  have hjump_zero : Tendsto (fun q : ℝ =>
      ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) / q ∂ν) atTop (nhds 0) := by
    have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := ν.restrict (Set.Ioi (0 : ℝ)))
      (F := fun (q : ℝ) (x : ℝ) => (1 - Real.exp (-q * x)) / q)
      (f := fun _ : ℝ => (0 : ℝ))
      (bound := fun x : ℝ => min (1 : ℝ) x)
      (l := atTop)
      (Eventually.of_forall fun q =>
        ((continuous_const.sub (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).div_const q).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxpos : 0 < x := hx
        have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
        have hnn : 0 ≤ (1 - Real.exp (-q * x)) / q := by
          apply div_nonneg _ hqpos.le
          have : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        refine le_min ?_ ?_
        · rw [div_le_one hqpos]
          have : 0 < Real.exp (-q * x) := Real.exp_pos _
          linarith
        · rw [div_le_iff₀ hqpos]
          have := Real.add_one_le_exp (-q * x)
          linarith)
      hmin_x
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxpos : 0 < x := hx
        refine squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun q : ℝ => 1 / q) atTop (nhds 0))
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
          apply div_nonneg _ hq.le
          have : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
          apply div_le_div_of_nonneg_right _ hq.le
          have : 0 < Real.exp (-q * x) := Real.exp_pos _
          linarith)
    simpa only [integral_zero] using hlim
  have hadd : Tendsto (fun q : ℝ =>
      d + ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) / q ∂ν) atTop (nhds d) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := d)).add hjump_zero
  refine hadd.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  rw [add_div, mul_div_cancel_right₀ d hq.ne', integral_div]

/-! ### Part (1): Laplace exponent via analytic continuation and Maximum Modulus Principle -/

private lemma part_one_laplace_exponent
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hsub : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    (hν_neg : ν (Set.Iio (0 : ℝ)) = 0)
    (hσ : σ = 0)
    (hmin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (ν.restrict (Set.Ioi (0 : ℝ))))
    (hd_nonneg : 0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν) :
    let d : ℝ := -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν
    ∀ q : ℝ, 0 ≤ q →
      ∫ ω, Real.exp (-q * X 1 ω) ∂P =
        Real.exp (-(d * q + ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν)) := by
  intro d q hq
  by_cases hq0 : q = 0
  · subst hq0
    simp
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hX1_ae : AEMeasurable (X 1) P := by
    by_contra hnot
    have h0 : P.map (X 1) = 0 := Measure.map_of_not_aemeasurable hnot
    have hc := hchar 1 0
    rw [h0] at hc
    simp [Kyprianou.Ch01.levyTripleExponent, ProbabilityTheory.levyCompensatedIntegrand] at hc
  have hX1_nonneg : ∀ᵐ ω ∂P, 0 ≤ X 1 ω := by
    filter_upwards [hsub] with ω hω
    have h0 : X 0 ω = 0 := congrFun hX.start_zero ω
    have hle : X 0 ω ≤ X 1 ω := hω (bot_le : (0 : ℝ≥0) ≤ 1)
    linarith
  let μ : Measure ℝ := P.map (X 1)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hX1_ae
  have hμ_nonneg : ∀ᵐ x ∂μ, 0 ≤ x := by
    have hmem : ∀ᵐ x ∂μ, x ∈ Set.Ici (0 : ℝ) :=
      (ae_map_iff hX1_ae measurableSet_Ici).mpr hX1_nonneg
    exact hmem
  have hmin_x : Integrable (fun x : ℝ => min (1 : ℝ) x) (ν.restrict (Set.Ioi (0 : ℝ))) :=
    integrable_min_one_id_Ioi hmin
  have hx_Ioo : IntegrableOn (fun x : ℝ => x) (Set.Ioo (0 : ℝ) 1) ν :=
    integrableOn_id_Ioo_of_min hmin
  have hrestrict_ν : ν.restrict (Set.Ioi (0 : ℝ)) = ν :=
    restrict_Ioi_eq_self_of_subordinator hν hν_neg
  let F : ℂ → ℂ := fun z => ∫ x, Complex.exp (Complex.I * z * (x : ℂ)) ∂μ
  let Ψ : ℂ → ℂ := fun z =>
    Complex.I * (d : ℂ) * z +
      ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (x : ℂ)) - 1) ∂ν
  let G : ℂ → ℂ := fun z => Complex.exp (Ψ z)
  let Hcl : Set ℂ := {z : ℂ | 0 ≤ z.im}
  let Hop : Set ℂ := {z : ℂ | 0 < z.im}
  -- Integrability of the Lévy integrand on Ioi 0 for z ∈ Hcl
  have hΨ_int : ∀ z ∈ Hcl,
      Integrable (fun x : ℝ => Complex.exp (Complex.I * z * (x : ℂ)) - 1)
        (ν.restrict (Set.Ioi (0 : ℝ))) := by
    intro z hz
    refine Integrable.mono' (hmin_x.const_mul (max 2 ‖z‖)) ?_ ?_
    · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).sub
        continuous_const).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_cexp_I_mul_mul_sub_one_le hz hx.le
  -- Boundary agreement: F ξ = G ξ for all ξ : ℝ
  have hboundary : ∀ ξ : ℝ, F (ξ : ℂ) = G (ξ : ℂ) := by
    intro ξ
    have hFξ : F (ξ : ℂ) = charFun μ ξ := by
      rw [charFun_apply_real]
      dsimp [F]
      congr 1; ext x; congr 1; ring
    have hΨξ : Ψ (ξ : ℂ) = Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ := by
      dsimp [Ψ, Kyprianou.Ch01.levyTripleExponent]
      rw [hσ]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, NNReal.coe_zero,
        zero_mul, zero_div, Complex.ofReal_zero, sub_zero]
      rw [← hrestrict_ν]
      have hcomp_eq : ∀ x ∈ Set.Ioi (0 : ℝ),
          ProbabilityTheory.levyCompensatedIntegrand ξ x =
            (Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ)) - 1) -
              (Set.Ioo (0 : ℝ) 1).indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ)) x := by
        intro x hx
        have hxpos : 0 < x := hx
        dsimp [ProbabilityTheory.levyCompensatedIntegrand]
        by_cases hx1 : x < 1
        · have habs : |x| < 1 := by rwa [abs_of_pos hxpos]
          have hmem : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hxpos, hx1⟩
          rw [if_pos habs, Set.indicator_of_mem hmem]
          ring_nf
        · have habs : ¬ |x| < 1 := by rwa [abs_of_pos hxpos]
          have hmem : x ∉ Set.Ioo (0 : ℝ) 1 := fun h => hx1 h.2
          rw [if_neg habs, Set.indicator_of_notMem hmem]
          ring_nf
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcomp_eq]
      have hint1 := hΨ_int (ξ : ℂ) (by simp [Hcl])
      have hint2 : Integrable
          ((Set.Ioo (0 : ℝ) 1).indicator (fun y : ℝ => Complex.I * (ξ : ℂ) * (y : ℂ)))
          (ν.restrict (Set.Ioi (0 : ℝ))) := by
        rw [integrable_indicator_iff measurableSet_Ioo]
        unfold IntegrableOn
        rw [Measure.restrict_restrict measurableSet_Ioo,
          Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self]
        exact (Complex.ofRealCLM.integrable_comp hx_Ioo).const_mul (Complex.I * (ξ : ℂ))
      have hcast_ioo : (∫ a in Set.Ioo (0 : ℝ) 1, (a : ℂ) ∂ν) =
          ((∫ a in Set.Ioo (0 : ℝ) 1, a ∂ν : ℝ) : ℂ) := integral_ofReal
      rw [integral_sub hint1 hint2, integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo,
        Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self,
        integral_const_mul, hcast_ioo]
      simp only [hrestrict_ν]
      dsimp [d]
      push_cast
      ring
    rw [hFξ, hchar 1 ξ]
    dsimp [G]
    rw [hΨξ]
    simp
  -- Uniform norm bounds on Hcl: ‖F z‖ ≤ 1 and ‖G z‖ ≤ 1
  have hF_norm : ∀ z ∈ Hcl, ‖F z‖ ≤ 1 := by
    intro z hz
    calc ‖F z‖ ≤ ∫ x, ‖Complex.exp (Complex.I * z * (x : ℂ))‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _, (1 : ℝ) ∂μ := by
        refine integral_mono_ae ?_ (integrable_const (1 : ℝ)) ?_
        · refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
          · exact (Complex.continuous_exp.comp
              (continuous_const.mul Complex.continuous_ofReal)).norm.aestronglyMeasurable
          · filter_upwards [hμ_nonneg] with x hx
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            exact norm_cexp_I_mul_mul_ofReal_le_one hz hx
        · filter_upwards [hμ_nonneg] with x hx
          exact norm_cexp_I_mul_mul_ofReal_le_one hz hx
      _ = 1 := by simp
  have hG_norm : ∀ z ∈ Hcl, ‖G z‖ ≤ 1 := by
    intro z hz
    dsimp [G]
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    dsimp [Ψ]
    have hlin : (Complex.I * (d : ℂ) * z).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.mul_im]
      have hzim : 0 ≤ z.im := hz
      nlinarith [hd_nonneg, hzim]
    have hjmp : (∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (x : ℂ)) - 1) ∂ν).re ≤ 0 := by
      have hre_comm : (∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (x : ℂ)) - 1) ∂ν).re =
          ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (x : ℂ)) - 1).re ∂ν :=
        (Complex.reCLM.integral_comp_comm (hΨ_int z hz)).symm
      rw [hre_comm]
      refine integral_nonpos_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hx
      change (Complex.exp (Complex.I * z * (x : ℂ)) - 1).re ≤ 0
      rw [Complex.sub_re, Complex.one_re]
      have hle := Complex.re_le_norm (Complex.exp (Complex.I * z * (x : ℂ)))
      have hle1 := norm_cexp_I_mul_mul_ofReal_le_one hz hxpos.le
      linarith
    linarith
  -- Continuity of F and G on Hcl
  have hF_cont : ContinuousOn F Hcl := by
    refine MeasureTheory.continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const (1 : ℝ)) ?_
    · intro z _
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
    · intro z hz
      filter_upwards [hμ_nonneg] with x hx
      exact norm_cexp_I_mul_mul_ofReal_le_one hz hx
    · refine ae_of_all _ fun x => ?_
      exact (Complex.continuous_exp.comp
        ((continuous_const.mul continuous_id).mul continuous_const)).continuousOn
  have hG_cont : ContinuousOn G Hcl := by
    refine Complex.continuous_exp.comp_continuousOn ?_
    refine (continuous_const.mul continuous_id).continuousOn.add ?_
    intro z₀ hz₀
    let s : Set ℂ := Hcl ∩ Metric.ball z₀ 1
    have hs_cont : ContinuousOn
        (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (Complex.I * z * (x : ℂ)) - 1) ∂ν) s := by
      refine MeasureTheory.continuousOn_of_dominated
        (bound := fun x : ℝ => max 2 (‖z₀‖ + 1) * min 1 x) ?_ ?_ (hmin_x.const_mul _) ?_
      · intro z _
        exact ((Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).sub continuous_const).aestronglyMeasurable
      · intro z hz
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
          have hdist : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz.2
          have := norm_sub_norm_le z z₀
          linarith
        calc ‖Complex.exp (Complex.I * z * (x : ℂ)) - 1‖
            ≤ max 2 ‖z‖ * min 1 x := norm_cexp_I_mul_mul_sub_one_le hz.1 hx.le
          _ ≤ max 2 (‖z₀‖ + 1) * min 1 x :=
              mul_le_mul_of_nonneg_right (max_le_max le_rfl hz_norm) (le_min zero_le_one hx.le)
      · refine ae_of_all _ fun x => ?_
        exact ((Complex.continuous_exp.comp
          ((continuous_const.mul continuous_id).mul continuous_const)).sub
          continuous_const).continuousOn
    have hnhds : s ∈ nhdsWithin z₀ Hcl :=
      inter_mem_nhdsWithin Hcl (Metric.ball_mem_nhds z₀ one_pos)
    exact (hs_cont z₀ ⟨hz₀, Metric.mem_ball_self one_pos⟩).mono_of_mem_nhdsWithin hnhds
  -- Holomorphicity of F and G on Hop
  have hF_diff : DifferentiableOn ℂ F Hop := by
    intro z₀ hz₀
    let ε : ℝ := z₀.im / 2
    have hε : 0 < ε := half_pos hz₀
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ)
      (F := fun (z : ℂ) (x : ℝ) => Complex.exp (Complex.I * z * (x : ℂ)))
      (F' := fun (z : ℂ) (x : ℝ) => Complex.I * (x : ℂ) * Complex.exp (Complex.I * z * (x : ℂ)))
      (bound := fun _ : ℝ => 1 / ε)
      (x₀ := z₀) (s := Metric.ball z₀ ε)
      (Metric.ball_mem_nhds z₀ hε)
      (Eventually.of_forall fun z =>
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
      (by
        refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
        · exact (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
        · filter_upwards [hμ_nonneg] with x hx
          exact norm_cexp_I_mul_mul_ofReal_le_one hz₀.le hx)
      ((continuous_const.mul Complex.continuous_ofReal).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
      (by
        filter_upwards [hμ_nonneg] with x hx z hz
        have hzim : ε ≤ z.im := by
          have hdist : ‖z - z₀‖ < ε := by simpa [dist_eq_norm] using hz
          have him : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
            simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
          have hε_eq : ε = z₀.im / 2 := rfl
          linarith [(abs_le.mp (him.trans hdist.le)).1, hε_eq]
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx, norm_cexp_I_mul_mul_ofReal]
        calc x * Real.exp (-z.im * x)
            ≤ x * Real.exp (-ε * x) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hx
          _ ≤ 1 / ε := mul_exp_neg_le_inv hε hx)
      (integrable_const (1 / ε))
      (ae_of_all _ fun x z _ => by
        have h1 : HasDerivAt (fun w : ℂ => Complex.I * w * (x : ℂ)) (Complex.I * (x : ℂ)) z := by
          have := ((hasDerivAt_id z).const_mul Complex.I).mul_const (x : ℂ)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simpa [mul_comm, mul_left_comm, mul_assoc] using h1.cexp)
    exact hderiv.2.differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ G Hop := by
    intro z₀ hz₀
    let ε : ℝ := z₀.im / 2
    have hε : 0 < ε := half_pos hz₀
    have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν.restrict (Set.Ioi (0 : ℝ)))
      (F := fun (z : ℂ) (x : ℝ) => Complex.exp (Complex.I * z * (x : ℂ)) - 1)
      (F' := fun (z : ℂ) (x : ℝ) => Complex.I * (x : ℂ) * Complex.exp (Complex.I * z * (x : ℂ)))
      (bound := fun x : ℝ => max 1 (1 / ε) * min 1 x)
      (x₀ := z₀) (s := Metric.ball z₀ ε)
      (Metric.ball_mem_nhds z₀ hε)
      (Eventually.of_forall fun z =>
        ((Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).sub continuous_const).aestronglyMeasurable)
      (hΨ_int z₀ (show 0 ≤ z₀.im from le_of_lt hz₀))
      ((continuous_const.mul Complex.continuous_ofReal).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
        have hxpos : 0 < x := hx
        have hzim : ε ≤ z.im := by
          have hdist : ‖z - z₀‖ < ε := by simpa [dist_eq_norm] using hz
          have him : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
            simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
          have hε_eq : ε = z₀.im / 2 := rfl
          linarith [(abs_le.mp (him.trans hdist.le)).1, hε_eq]
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hxpos, norm_cexp_I_mul_mul_ofReal]
        by_cases hx1 : x ≤ 1
        · rw [min_eq_right hx1]
          have hexp : Real.exp (-z.im * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          calc x * Real.exp (-z.im * x) ≤ x * 1 := mul_le_mul_of_nonneg_left hexp hxpos.le
            _ = 1 * x := by ring
            _ ≤ max 1 (1 / ε) * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le
        · push Not at hx1
          rw [min_eq_left hx1.le, mul_one]
          calc x * Real.exp (-z.im * x)
              ≤ x * Real.exp (-ε * x) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hxpos.le
            _ ≤ 1 / ε := mul_exp_neg_le_inv hε hxpos.le
            _ ≤ max 1 (1 / ε) := le_max_right _ _)
      (hmin_x.const_mul (max 1 (1 / ε)))
      (ae_of_all _ fun x z _ => by
        have h1 : HasDerivAt (fun w : ℂ => Complex.I * w * (x : ℂ)) (Complex.I * (x : ℂ)) z := by
          have := ((hasDerivAt_id z).const_mul Complex.I).mul_const (x : ℂ)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simpa [mul_comm, mul_left_comm, mul_assoc] using (h1.cexp).sub_const 1)
    have hΨ_diffAt : DifferentiableAt ℂ Ψ z₀ :=
      ((differentiableAt_id.const_mul (Complex.I * (d : ℂ))).add hderiv.2.differentiableAt)
    exact (Complex.differentiableAt_exp.comp z₀ hΨ_diffAt).differentiableWithinAt
  -- Maximum Modulus Principle on half-disks U_R = {w | 0 < w.im ∧ ‖w‖ < R}
  let K : ℂ → ℂ := fun w => (F w - G w) / (w + Complex.I)
  have hK_zero : ∀ z₀ ∈ Hop, F z₀ = G z₀ := by
    intro z₀ hz₀
    have hK_le : ∀ R : ℝ, max (‖z₀‖ + 1) 1 < R → ‖K z₀‖ ≤ 2 / R := by
      intro R hR
      have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hR.le)
      have hz₀_lt : ‖z₀‖ < R := by linarith [le_max_left (‖z₀‖ + 1) 1]
      let U : Set ℂ := {w : ℂ | 0 < w.im ∧ ‖w‖ < R}
      have hU_bdd : Bornology.IsBounded U :=
        Metric.isBounded_iff_subset_closedBall 0 |>.mpr
          ⟨R, fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2.le⟩
      have hU_sub_Hop : U ⊆ Hop := fun w hw => hw.1
      have hcl_sub : closure U ⊆ {w : ℂ | 0 ≤ w.im ∧ ‖w‖ ≤ R} := by
        refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩) ?_
        exact (isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le continuous_norm continuous_const)
      have hden_ne : ∀ w ∈ closure U, w + Complex.I ≠ 0 := by
        intro w hw heq
        have him : (w + Complex.I).im = 0 := by rw [heq]; simp
        simp only [Complex.add_im, Complex.I_im] at him
        linarith [(hcl_sub hw).1]
      have hK_diffCont : DiffContOnCl ℂ K U := by
        refine ⟨?_, ?_⟩
        · refine ((hF_diff.mono hU_sub_Hop).sub (hG_diff.mono hU_sub_Hop)).div
            (differentiableOn_id.add (differentiableOn_const Complex.I)) ?_
          intro w hw
          exact hden_ne w (subset_closure hw)
        · refine ((hF_cont.mono fun w hw => (hcl_sub hw).1).sub
            (hG_cont.mono fun w hw => (hcl_sub hw).1)).div
            (continuousOn_id.add continuousOn_const) hden_ne
      have hfront : ∀ w ∈ frontier U, ‖K w‖ ≤ 2 / R := by
        intro w hw
        have hw_cl : 0 ≤ w.im ∧ ‖w‖ ≤ R := hcl_sub hw.1
        have hU_open : IsOpen U :=
          (isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt continuous_norm continuous_const)
        have hw_notU : w ∉ U := by
          have := hw.2
          rwa [hU_open.interior_eq] at this
        by_cases him0 : w.im = 0
        · have hw_real : w = (w.re : ℂ) := by
            apply Complex.ext <;> simp [him0]
          have hFG : F w = G w := by rw [hw_real]; exact hboundary w.re
          simp only [K, hFG, sub_self, zero_div, norm_zero]
          positivity
        · have him_pos : 0 < w.im := lt_of_le_of_ne hw_cl.1 (Ne.symm him0)
          have hnorm_eq : ‖w‖ = R := by
            have : ¬ ‖w‖ < R := fun hlt => hw_notU ⟨him_pos, hlt⟩
            linarith
          have hden_ge : R ≤ ‖w + Complex.I‖ := by
            rw [← hnorm_eq]
            have hsq : ‖w‖ ^ 2 ≤ ‖w + Complex.I‖ ^ 2 := by
              rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
              simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
              nlinarith [hw_cl.1]
            nlinarith [norm_nonneg w, norm_nonneg (w + Complex.I)]
          have hnum_le : ‖F w - G w‖ ≤ 2 := by
            calc ‖F w - G w‖ ≤ ‖F w‖ + ‖G w‖ := norm_sub_le _ _
              _ ≤ 1 + 1 := add_le_add (hF_norm w hw_cl.1) (hG_norm w hw_cl.1)
              _ = 2 := by norm_num
          rw [show K w = (F w - G w) / (w + Complex.I) from rfl, norm_div]
          calc ‖F w - G w‖ / ‖w + Complex.I‖
              ≤ 2 / ‖w + Complex.I‖ := div_le_div_of_nonneg_right hnum_le (norm_nonneg _)
            _ ≤ 2 / R := div_le_div_of_nonneg_left (by norm_num) hR_pos hden_ge
      exact Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hK_diffCont hfront
        (subset_closure ⟨hz₀, hz₀_lt⟩)
    have hK_norm_zero : ‖K z₀‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      have htend : Tendsto (fun R : ℝ => 2 / R) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine ge_of_tendsto htend ?_
      filter_upwards [eventually_gt_atTop (max (‖z₀‖ + 1) 1)] with R hR
      exact hK_le R hR
    have hKz0 : K z₀ = 0 := norm_eq_zero.mp hK_norm_zero
    have hden0 : z₀ + Complex.I ≠ 0 := by
      intro heq
      have him : (z₀ + Complex.I).im = 0 := by rw [heq]; simp
      simp only [Complex.add_im, Complex.I_im] at him
      linarith [show 0 < z₀.im from hz₀]
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hKz0).resolve_right hden0)
  -- Specialize to z₀ = q * I
  have hqi_mem : (q : ℂ) * Complex.I ∈ Hop := by
    change 0 < ((q : ℂ) * Complex.I).im
    simpa using hqpos
  have heq := hK_zero ((q : ℂ) * Complex.I) hqi_mem
  have hF_qi : F ((q : ℂ) * Complex.I) = ((∫ ω, Real.exp (-q * X 1 ω) ∂P : ℝ) : ℂ) := by
    have hmul : ∀ x : ℝ, Complex.I * ((q : ℂ) * Complex.I) * (x : ℂ) = ((-q * x : ℝ) : ℂ) := by
      intro x
      calc Complex.I * ((q : ℂ) * Complex.I) * (x : ℂ)
          = (Complex.I * Complex.I) * ((q : ℂ) * (x : ℂ)) := by ring
        _ = (-1) * ((q : ℂ) * (x : ℂ)) := by rw [Complex.I_mul_I]
        _ = ((-q * x : ℝ) : ℂ) := by push_cast; ring
    have hF_int_real : F ((q : ℂ) * Complex.I) = ((∫ x, Real.exp (-q * x) ∂μ : ℝ) : ℂ) := by
      dsimp [F]
      simp_rw [hmul, ← Complex.ofReal_exp]
      have hint_r : Integrable (fun x : ℝ => Real.exp (-q * x)) μ := by
        refine Integrable.mono' (integrable_const (1 : ℝ))
          (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
        filter_upwards [hμ_nonneg] with x hx
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      exact Complex.ofRealCLM.integral_comp_comm hint_r
    rw [hF_int_real]
    congr 1
    exact MeasureTheory.integral_map hX1_ae
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hG_qi : G ((q : ℂ) * Complex.I) =
      ((Real.exp (-(d * q + ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν)) : ℝ) : ℂ) := by
    have hmul : ∀ x : ℝ, Complex.I * ((q : ℂ) * Complex.I) * (x : ℂ) = ((-q * x : ℝ) : ℂ) := by
      intro x
      calc Complex.I * ((q : ℂ) * Complex.I) * (x : ℂ)
          = (Complex.I * Complex.I) * ((q : ℂ) * (x : ℂ)) := by ring
        _ = (-1) * ((q : ℂ) * (x : ℂ)) := by rw [Complex.I_mul_I]
        _ = ((-q * x : ℝ) : ℂ) := by push_cast; ring
    have hlin : Complex.I * (d : ℂ) * ((q : ℂ) * Complex.I) = ((-(d * q) : ℝ) : ℂ) := by
      calc Complex.I * (d : ℂ) * ((q : ℂ) * Complex.I)
          = (Complex.I * Complex.I) * ((d : ℂ) * (q : ℂ)) := by ring
        _ = (-1) * ((d : ℂ) * (q : ℂ)) := by rw [Complex.I_mul_I]
        _ = ((-(d * q) : ℝ) : ℂ) := by push_cast; ring
    have hint_real : Integrable (fun x : ℝ => 1 - Real.exp (-q * x))
        (ν.restrict (Set.Ioi (0 : ℝ))) := by
      refine Integrable.mono' (hmin_x.const_mul (max 1 q))
        (continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := hx
      have hnn : 0 ≤ 1 - Real.exp (-q * x) := by
        have : Real.exp (-q * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      by_cases hx1 : x ≤ 1
      · rw [min_eq_right hx1]
        have h1 : 1 - Real.exp (-q * x) ≤ q * x := by
          have := Real.add_one_le_exp (-q * x); linarith
        exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_right 1 q) hxpos.le)
      · push Not at hx1
        rw [min_eq_left hx1.le, mul_one]
        have h1 : 1 - Real.exp (-q * x) ≤ 1 := by linarith [Real.exp_pos (-q * x)]
        exact le_trans h1 (le_max_left 1 q)
    have hΨ_qi : Ψ ((q : ℂ) * Complex.I) =
        ((-(d * q + ∫ x in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * x)) ∂ν) : ℝ) : ℂ) := by
      dsimp [Ψ]
      rw [hlin]
      have hrew : (fun x : ℝ => Complex.exp (Complex.I * ((q : ℂ) * Complex.I) * (x : ℂ)) - 1) =
          fun x : ℝ => -(((1 - Real.exp (-q * x) : ℝ) : ℂ)) := by
        ext x
        rw [hmul x, ← Complex.ofReal_exp]
        push_cast; ring
      have hcast_ioi : (∫ a in Set.Ioi (0 : ℝ), ((1 - Real.exp (-q * a) : ℝ) : ℂ) ∂ν) =
          ((∫ a in Set.Ioi (0 : ℝ), (1 - Real.exp (-q * a)) ∂ν : ℝ) : ℂ) := integral_ofReal
      rw [hrew, integral_neg, hcast_ioi]
      push_cast; ring
    dsimp [G]
    rw [hΨ_qi, Complex.ofReal_exp]
  rw [hF_qi, hG_qi] at heq
  exact Complex.ofReal_injective heq

end Exercise211Helpers

theorem solution
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hsub : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ)) :
    let d : ℝ := -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν
    (∀ q : ℝ, 0 ≤ q →
       ∫ ω, Real.exp (-q * X 1 ω) ∂P =
       Real.exp (-(d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν))) ∧
    (∀ q : ℝ, 0 < q →
       ∫ x in Set.Ioi (0 : ℝ),
          (1 - Real.exp (-q * x)) ∂ν =
       q * ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-q * x) * (ν (Set.Ioi x)).toReal ∂volume) ∧
    Tendsto (fun q : ℝ =>
       (d * q +
         ∫ x in Set.Ioi (0 : ℝ),
           (1 - Real.exp (-q * x)) ∂ν) / q)
       atTop (nhds d) := by
  obtain ⟨hν_neg, hσ, hmin, hd_nonneg⟩ :=
    (Kyprianou.subordinatorCriterionCh02V3 a σ ν hν P X hX hchar).mp hsub
  refine ⟨?_, ?_, ?_⟩
  · exact Exercise211Helpers.part_one_laplace_exponent
      a σ ν hν P X hX hsub hchar hν_neg hσ hmin hd_nonneg
  · intro q hq
    exact Exercise211Helpers.part_two_tail_identity hν hq
  · exact Exercise211Helpers.part_three_drift_recovery hmin
      (-a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν)
