-- Prove2me | solution 1 for MartOT.Curtain.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:15:44.884536+00:00
-- url     : https://prove2.me/submissions/4d4aa28f-1ea1-4c7f-bc48-178f0fcf3d40

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

section Helpers

private noncomputable def rderiv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (Ioi x) x

private noncomputable def lderiv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin f (Iio x) x

private noncomputable def mass (μ : Measure ℝ) : ℝ :=
  (μ univ).toReal

private noncomputable def mean (μ : Measure ℝ) : ℝ :=
  ∫ y, y ∂μ

/-! ### Section 1: 1D convex functions, right/left derivatives, FTC, Stieltjes measure, representation -/

private lemma convex_continuous {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) : Continuous f :=
  continuousOn_univ.mp (hf.continuousOn isOpen_univ)

private lemma convex_hasDerivWithinAt_rderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (rderiv f x) (Ioi x) x :=
  hf.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

private lemma convex_hasDerivWithinAt_lderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    HasDerivWithinAt f (lderiv f x) (Iio x) x :=
  hf.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)

private lemma convex_monotone_rderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    Monotone (rderiv f) := by
  intro x y hxy
  exact hf.monotoneOn_rightDeriv (by simp) (by simp) hxy

private lemma convex_monotone_lderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    Monotone (lderiv f) := by
  intro x y hxy
  exact hf.monotoneOn_leftDeriv (by simp) (by simp) hxy

private lemma convex_lderiv_le_rderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    lderiv f x ≤ rderiv f x :=
  hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

private lemma convex_rderiv_le_slope {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {x y : ℝ}
    (hxy : x < y) : rderiv f x ≤ slope f x y :=
  hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) hxy

private lemma convex_slope_le_lderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {x y : ℝ}
    (hxy : x < y) : slope f x y ≤ lderiv f y :=
  hf.slope_le_leftDeriv_of_mem_interior (mem_univ x) (by simp) hxy

private lemma convex_rderiv_le_lderiv_of_lt {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {x y : ℝ}
    (hxy : x < y) : rderiv f x ≤ lderiv f y :=
  (convex_rderiv_le_slope hf hxy).trans (convex_slope_le_lderiv hf hxy)

private lemma convex_subgradient_rderiv {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x t : ℝ) :
    f x + rderiv f x * (t - x) ≤ f t := by
  rcases lt_trichotomy x t with hlt | rfl | hgt
  · have h := convex_rderiv_le_slope hf hlt
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hlt)] at h
    linarith
  · simp
  · have h := (convex_slope_le_lderiv hf hgt).trans (convex_lderiv_le_rderiv hf x)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hgt)] at h
    linarith

private lemma convex_rderiv_rightContinuous {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    ContinuousWithinAt (rderiv f) (Ici x) x := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hderiv := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
    (convex_hasDerivWithinAt_rderiv hf x)
  rw [Metric.tendsto_nhdsWithin_nhds] at hderiv
  obtain ⟨δ₁, hδ₁, hslope⟩ := hderiv (ε / 2) (half_pos hε)
  let z : ℝ := x + δ₁ / 2
  have hxz : x < z := by dsimp [z]; linarith
  have hslope_z : slope f x z < rderiv f x + ε / 2 := by
    have hz_dist : dist z x < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      dsimp [z]; linarith
    have h := hslope (mem_Ioi.mpr hxz) hz_dist
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).2]
  have hcont_slope : ContinuousAt (fun y => (f z - f y) / (z - y)) x := by
    refine ContinuousAt.div ?_ ?_ (sub_ne_zero.mpr hxz.ne')
    · exact continuousAt_const.sub (convex_continuous hf).continuousAt
    · exact continuousAt_const.sub continuousAt_id
  have hlt_at_x : (f z - f x) / (z - x) < rderiv f x + ε := by
    have : (f z - f x) / (z - x) = slope f x z := by rw [slope_def_field]
    linarith
  have hev := hcont_slope.eventually (gt_mem_nhds hlt_at_x)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₂, hδ₂, hball⟩ := hev
  refine ⟨min δ₂ (z - x), lt_min hδ₂ (sub_pos.mpr hxz), fun y hy hdist => ?_⟩
  have hxy : x ≤ y := hy
  have hyz : y < z := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hdist
    linarith [lt_of_lt_of_le hdist (min_le_right _ _)]
  have hdist₂ : dist y x < δ₂ := lt_of_lt_of_le hdist (min_le_left _ _)
  have h1 : rderiv f x ≤ rderiv f y := convex_monotone_rderiv hf hxy
  have h2 : rderiv f y ≤ slope f y z := convex_rderiv_le_slope hf hyz
  have h3 : slope f y z < rderiv f x + ε := by
    rw [slope_def_field]
    exact hball hdist₂
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

private noncomputable def convexStieltjes {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    StieltjesFunction ℝ where
  toFun := rderiv f
  mono' := convex_monotone_rderiv hf
  right_continuous' := convex_rderiv_rightContinuous hf

private noncomputable def convexHalfStieltjes {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) :
    StieltjesFunction ℝ :=
  ((1 / 2 : ℝ≥0) : ℝ≥0) • convexStieltjes hf

@[simp]
private lemma convexHalfStieltjes_apply {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (x : ℝ) :
    convexHalfStieltjes hf x = rderiv f x / 2 := by
  change ((1 / 2 : ℝ≥0) : ℝ) * rderiv f x = rderiv f x / 2
  push_cast
  ring

private lemma convex_ftc {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, rderiv f t = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (convex_continuous hf).continuousOn
    (fun x _ => convex_hasDerivWithinAt_rderiv hf x)
    (convex_monotone_rderiv hf).intervalIntegrable

private lemma stieltjes_sigmaFinite (g : StieltjesFunction ℝ) : SigmaFinite g.measure := by
  have : IsLocallyFiniteMeasure g.measure := by
    refine ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩⟩
    exact lt_of_le_of_lt (measure_mono Ioo_subset_Ioc_self) (by rw [g.measure_Ioc]; exact ENNReal.ofReal_lt_top)
  infer_instance

private lemma convex_repr {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (y : ℝ) :
    ENNReal.ofReal (f y - f 0 - rderiv f 0 * y) =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂(convexStieltjes hf).measure) +
      (∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂(convexStieltjes hf).measure) := by
  set σ : Measure ℝ := (convexStieltjes hf).measure
  have : SigmaFinite σ := stieltjes_sigmaFinite (convexStieltjes hf)
  rcases le_or_gt 0 y with hy | hy
  · have hneg : ∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂σ = 0 := by
      refine (setLIntegral_eq_zero_iff measurableSet_Iic (by fun_prop)).mpr ?_
      filter_upwards with s hs
      have : s - y ≤ 0 := by linarith [mem_Iic.mp hs]
      simp [max_eq_right this]
    rw [hneg, add_zero]
    let A : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ y}
    have hA : MeasurableSet A := by
      have : A = (Ioi 0 ×ˢ univ) ∩ {p : ℝ × ℝ | p.1 ≤ p.2} ∩ (univ ×ˢ Iic y) := by
        ext ⟨s, t⟩; simp [A, and_assoc]
      rw [this]
      exact ((measurableSet_Ioi.prod MeasurableSet.univ).inter
        (measurableSet_le measurable_fst measurable_snd)).inter
        (MeasurableSet.univ.prod measurableSet_Iic)
    have hLHS : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂σ =
        ∫⁻ s, ∫⁻ t, A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t) ∂volume ∂σ := by
      rw [← lintegral_indicator measurableSet_Ioi]
      congr 1; ext s
      by_cases hs : s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hs]
        have hs' : 0 < s := mem_Ioi.mp hs
        have hsec : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) =
            (Icc s y).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext t; by_cases ht : s ≤ t ∧ t ≤ y <;> simp [A, hs', ht]
        rw [hsec, lintegral_indicator measurableSet_Icc, setLIntegral_one, Real.volume_Icc]
        rcases le_or_gt s y with hsy | hsy
        · rw [max_eq_left (sub_nonneg.mpr hsy)]
        · rw [max_eq_right (by linarith), ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr (by linarith)]
      · rw [indicator_of_notMem hs]
        have hs' : ¬ 0 < s := hs
        have hzero : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) = fun _ => 0 := by
          ext t; simp [A, hs']
        rw [hzero, lintegral_zero]
    have hmeasA : AEMeasurable (Function.uncurry fun s t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t))
        (σ.prod volume) := (measurable_const.indicator hA).aemeasurable
    rw [hLHS, lintegral_lintegral_swap hmeasA]
    have hRHS : ∫⁻ t, ∫⁻ s, A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t) ∂σ ∂volume =
        ∫⁻ t in Ioc 0 y, ENNReal.ofReal (rderiv f t - rderiv f 0) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioc]
      congr 1; ext t
      by_cases ht : t ∈ Ioc 0 y
      · rw [indicator_of_mem ht]
        have hsec : (fun s => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) =
            (Ioc 0 t).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext s
          by_cases hs : 0 < s ∧ s ≤ t
          · simp [A, hs.1, hs.2, ht.2]
          · simp only [A, mem_Ioc, hs, not_false_eq_true, indicator_of_notMem]
            rw [indicator_of_notMem]
            intro ⟨h1, h2, _⟩; exact hs ⟨h1, h2⟩
        rw [hsec, lintegral_indicator measurableSet_Ioc, setLIntegral_one]
        exact (convexStieltjes hf).measure_Ioc 0 t
      · rw [indicator_of_notMem ht]
        have hzero : (fun s => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) = fun _ => 0 := by
          ext s
          rw [indicator_of_notMem]
          intro ⟨h1, h2, h3⟩
          exact ht ⟨lt_of_lt_of_le h1 h2, h3⟩
        rw [hzero, lintegral_zero]
    rw [hRHS]
    have hint : IntegrableOn (fun t => rderiv f t - rderiv f 0) (Ioc 0 y) volume := by
      have h1 := (convex_monotone_rderiv hf).intervalIntegrable (μ := volume) (a := 0) (b := y)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy] at h1
      exact h1.sub (integrableOn_const (by simp [Real.volume_Ioc]))
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioc 0 y)), 0 ≤ rderiv f t - rderiv f 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact sub_nonneg.mpr (convex_monotone_rderiv hf ht.1.le)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le hy, intervalIntegral.integral_sub
      (convex_monotone_rderiv hf).intervalIntegrable intervalIntegrable_const,
      convex_ftc hf hy, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · have hpos : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂σ = 0 := by
      refine (setLIntegral_eq_zero_iff measurableSet_Ioi (by fun_prop)).mpr ?_
      filter_upwards with s hs
      have : y - s ≤ 0 := by linarith [mem_Ioi.mp hs]
      simp [max_eq_right this]
    rw [hpos, zero_add]
    let A : Set (ℝ × ℝ) := {p | y ≤ p.2 ∧ p.2 < p.1 ∧ p.1 ≤ 0}
    have hA : MeasurableSet A := by
      have : A = (univ ×ˢ Ici y) ∩ {p : ℝ × ℝ | p.2 < p.1} ∩ (Iic 0 ×ˢ univ) := by
        ext ⟨s, t⟩; simp [A, and_assoc]
      rw [this]
      exact ((MeasurableSet.univ.prod measurableSet_Ici).inter
        (measurableSet_lt measurable_snd measurable_fst)).inter
        (measurableSet_Iic.prod MeasurableSet.univ)
    have hLHS : ∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂σ =
        ∫⁻ s, ∫⁻ t, A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t) ∂volume ∂σ := by
      rw [← lintegral_indicator measurableSet_Iic]
      congr 1; ext s
      by_cases hs : s ∈ Iic (0 : ℝ)
      · rw [indicator_of_mem hs]
        have hs' : s ≤ 0 := mem_Iic.mp hs
        have hsec : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) =
            (Ico y s).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext t; by_cases ht : y ≤ t ∧ t < s <;> simp [A, hs', ht]
        rw [hsec, lintegral_indicator measurableSet_Ico, setLIntegral_one, Real.volume_Ico]
        rcases le_or_gt y s with hys | hys
        · rw [max_eq_left (sub_nonneg.mpr hys)]
        · rw [max_eq_right (by linarith), ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr (by linarith)]
      · rw [indicator_of_notMem hs]
        have hs' : ¬ s ≤ 0 := hs
        have hzero : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) = fun _ => 0 := by
          ext t; simp [A, hs']
        rw [hzero, lintegral_zero]
    have hmeasA : AEMeasurable (Function.uncurry fun s t => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t))
        (σ.prod volume) := (measurable_const.indicator hA).aemeasurable
    rw [hLHS, lintegral_lintegral_swap hmeasA]
    have hRHS : ∫⁻ t, ∫⁻ s, A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t) ∂σ ∂volume =
        ∫⁻ t in Ico y 0, ENNReal.ofReal (rderiv f 0 - rderiv f t) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ico]
      congr 1; ext t
      by_cases ht : t ∈ Ico y 0
      · rw [indicator_of_mem ht]
        have hsec : (fun s => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) =
            (Ioc t 0).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext s
          by_cases hs : t < s ∧ s ≤ 0
          · simp [A, hs.1, hs.2, ht.1]
          · simp only [A, mem_Ioc, hs, not_false_eq_true, indicator_of_notMem]
            rw [indicator_of_notMem]
            intro ⟨_, h2, h3⟩; exact hs ⟨h2, h3⟩
        rw [hsec, lintegral_indicator measurableSet_Ioc, setLIntegral_one]
        exact (convexStieltjes hf).measure_Ioc t 0
      · rw [indicator_of_notMem ht]
        have hzero : (fun s => A.indicator (fun _ => (1 : ℝ≥0∞)) (s, t)) = fun _ => 0 := by
          ext s
          rw [indicator_of_notMem]
          intro ⟨h1, h2, h3⟩
          exact ht ⟨h1, lt_of_lt_of_le h2 h3⟩
        rw [hzero, lintegral_zero]
    rw [hRHS, setLIntegral_congr Ico_ae_eq_Ioc]
    have hint : IntegrableOn (fun t => rderiv f 0 - rderiv f t) (Ioc y 0) volume := by
      have h1 := (convex_monotone_rderiv hf).intervalIntegrable (μ := volume) (a := y) (b := 0)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le] at h1
      exact (integrableOn_const (by simp [Real.volume_Ioc])).sub h1
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioc y 0)), 0 ≤ rderiv f 0 - rderiv f t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact sub_nonneg.mpr (convex_monotone_rderiv hf ht.2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    congr 1
    rw [← intervalIntegral.integral_of_le hy.le, intervalIntegral.integral_sub
      intervalIntegrable_const (convex_monotone_rderiv hf).intervalIntegrable,
      convex_ftc hf hy.le, intervalIntegral.integral_const, smul_eq_mul]
    ring

/-! ### Section 2: Potential functions of measures in 𝓜 -/

private lemma inM_integrable_abs_sub {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    Integrable (fun y : ℝ => |y - x|) μ := by
  have := hμ.1
  have hbound : Integrable (fun y : ℝ => ‖y‖ + |x|) μ := hμ.2.norm.add (integrable_const |x|)
  refine hbound.mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
  exact abs_sub y x

private lemma inM_integrable_pos_sub {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (t : ℝ) :
    Integrable (fun y : ℝ => max (y - t) 0) μ := by
  have := hμ.1
  exact (inM_integrable_abs_sub hμ t).mono' (by fun_prop) (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _))

private lemma inM_integrable_sub_pos {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (t : ℝ) :
    Integrable (fun y : ℝ => max (t - y) 0) μ := by
  have := hμ.1
  exact (inM_integrable_abs_sub hμ t).mono' (by fun_prop) (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have : t - y ≤ |y - t| := by rw [abs_sub_comm]; exact le_abs_self _
    exact max_le this (abs_nonneg _))

private lemma potential_convex {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    ConvexOn ℝ univ (MartOT.Var.potential μ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, MartOT.Var.potential]
  have h1 : Integrable (fun z : ℝ => a * |z - x| + b * |z - y|) μ :=
    ((inM_integrable_abs_sub hμ x).const_mul a).add ((inM_integrable_abs_sub hμ y).const_mul b)
  calc
    ∫ z, |z - (a * x + b * y)| ∂μ
      ≤ ∫ z, (a * |z - x| + b * |z - y|) ∂μ := by
        refine integral_mono (inM_integrable_abs_sub hμ _) h1 fun z => ?_
        have hEq : z - (a * x + b * y) = a * (z - x) + b * (z - y) := by
          calc z - (a * x + b * y) = (a + b) * z - (a * x + b * y) := by rw [hab, one_mul]
            _ = a * (z - x) + b * (z - y) := by ring
        rw [hEq]
        calc |a * (z - x) + b * (z - y)|
            ≤ |a * (z - x)| + |b * (z - y)| := abs_add_le _ _
          _ = a * |z - x| + b * |z - y| := by
              rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * ∫ z, |z - x| ∂μ + b * ∫ z, |z - y| ∂μ := by
        rw [integral_add ((inM_integrable_abs_sub hμ x).const_mul a)
          ((inM_integrable_abs_sub hμ y).const_mul b),
          integral_const_mul, integral_const_mul]

private lemma potential_rderiv {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (x : ℝ) :
    rderiv (MartOT.Var.potential μ) x = 2 * (μ (Iic x)).toReal - mass μ := by
  have := hμ.1
  have hderiv : HasDerivWithinAt (MartOT.Var.potential μ)
      (2 * (μ (Iic x)).toReal - mass μ) (Ioi x) x := by
    rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
    let g : ℝ → ℝ := (Iic x).indicator (fun _ => (1 : ℝ)) - (Ioi x).indicator (fun _ => (1 : ℝ))
    have hg_int : ∫ y, g y ∂μ = 2 * (μ (Iic x)).toReal - mass μ := by
      have h1 : Integrable ((Iic x).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator measurableSet_Iic
      have h2 : Integrable ((Ioi x).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
        (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
      have hsub : ∫ y, g y ∂μ = (∫ y, (Iic x).indicator (fun _ => (1 : ℝ)) y ∂μ) -
          (∫ y, (Ioi x).indicator (fun _ => (1 : ℝ)) y ∂μ) := integral_sub h1 h2
      rw [hsub, integral_indicator_const _ measurableSet_Iic,
        integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
        Measure.real_def, Measure.real_def]
      have hcompl : μ (Ioi x) = μ univ - μ (Iic x) := by
        rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top μ _)]
      rw [hcompl, ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top μ _)]
      simp only [mass]
      ring
    rw [← hg_int]
    have hslope_eq : ∀ᶠ t in 𝓝[>] x,
        slope (MartOT.Var.potential μ) x t = ∫ y, (|y - t| - |y - x|) / (t - x) ∂μ := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
      rw [slope_def_field, MartOT.Var.potential, MartOT.Var.potential,
        ← integral_sub (inM_integrable_abs_sub hμ t) (inM_integrable_abs_sub hμ x),
        ← integral_div]
    refine (tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) ?_).congr' (hslope_eq.mono fun t ht => ht.symm)
    · exact Eventually.of_forall fun t => by fun_prop
    · filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sub_pos.mpr ht), div_le_one (sub_pos.mpr ht)]
      have h := abs_abs_sub_abs_le_abs_sub (y - t) (y - x)
      have : (y - t) - (y - x) = -(t - x) := by ring
      rw [this, abs_neg, abs_of_pos (sub_pos.mpr ht)] at h
      exact h
    · refine ae_of_all _ fun y => ?_
      by_cases hy : y ≤ x
      · have hconst : ∀ᶠ t in 𝓝[>] x, (|y - t| - |y - x|) / (t - x) = g y := by
          filter_upwards [self_mem_nhdsWithin] with t (ht : x < t)
          have h1 : |y - t| = t - y := by rw [abs_of_nonpos (by linarith)]; ring
          have h2 : |y - x| = x - y := by rw [abs_of_nonpos (by linarith)]; ring
          have hne : t - x ≠ 0 := (sub_pos.mpr ht).ne'
          have hg : g y = 1 := by simp [g, hy, not_lt.mpr hy]
          rw [h1, h2, hg]
          field_simp
          ring
        exact tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm)
      · push Not at hy
        have hconst : ∀ᶠ t in 𝓝[>] x, (|y - t| - |y - x|) / (t - x) = g y := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy)] with t (ht1 : x < t) (ht2 : t < y)
          have h1 : |y - t| = y - t := abs_of_pos (sub_pos.mpr ht2)
          have h2 : |y - x| = y - x := abs_of_pos (sub_pos.mpr hy)
          have hne : t - x ≠ 0 := (sub_pos.mpr ht1).ne'
          have hg : g y = -1 := by simp [g, not_le.mpr hy, hy]
          rw [h1, h2, hg]
          field_simp
          ring
        exact tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm)
  exact hderiv.derivWithin (uniqueDiffWithinAt_Ioi x)

private lemma halfStieltjes_potential_measure {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    (convexHalfStieltjes (potential_convex hμ)).measure = μ := by
  have := hμ.1
  have : IsLocallyFiniteMeasure (convexHalfStieltjes (potential_convex hμ)).measure := by
    refine ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩⟩
    exact lt_of_le_of_lt (measure_mono Ioo_subset_Ioc_self)
      (by rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_lt_top)
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [StieltjesFunction.measure_Ioc, convexHalfStieltjes_apply, convexHalfStieltjes_apply,
    potential_rderiv hμ b, potential_rderiv hμ a]
  have hsimp : (2 * (μ (Iic b)).toReal - mass μ) / 2 - (2 * (μ (Iic a)).toReal - mass μ) / 2 =
      (μ (Iic b)).toReal - (μ (Iic a)).toReal := by ring
  have hsdiff : Iic b \ Iic a = Ioc a b := by
    ext x; simp [and_comm]
  rw [hsimp, ← ENNReal.toReal_sub_of_le (measure_mono (Iic_subset_Iic.mpr hab.le))
    (measure_ne_top μ _), ENNReal.ofReal_toReal (by simp [measure_ne_top μ]),
    ← measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet
      (measure_ne_top μ _), hsdiff]

private lemma eq_of_potential_eq {μ₁ μ₂ : Measure ℝ} (h₁ : MartOT.Var.InM μ₁)
    (h₂ : MartOT.Var.InM μ₂) (h : ∀ x, MartOT.Var.potential μ₁ x = MartOT.Var.potential μ₂ x) :
    μ₁ = μ₂ := by
  have hfun : MartOT.Var.potential μ₁ = MartOT.Var.potential μ₂ := funext h
  rw [← halfStieltjes_potential_measure h₁, ← halfStieltjes_potential_measure h₂]
  congr 1
  ext x
  simp [convexHalfStieltjes_apply, rderiv, hfun]

private lemma potential_sub_pos_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (t : ℝ) :
    MartOT.Var.potential μ t - (mass μ * t - mean μ) = 2 * ∫ y, max (y - t) 0 ∂μ := by
  have := hμ.1
  have hlin : ∫ y, (t - y) ∂μ = mass μ * t - mean μ := by
    rw [integral_sub (integrable_const t) hμ.2, integral_const, smul_eq_mul]
    simp [mass, mean, Measure.real_def, mul_comm]
  have hsub_int : Integrable (fun y : ℝ => t - y) μ := (integrable_const t).sub hμ.2
  rw [MartOT.Var.potential, ← hlin,
    ← integral_sub (inM_integrable_abs_sub hμ t) hsub_int,
    ← integral_const_mul]
  congr 1; ext y
  rcases le_or_gt t y with hty | hty
  · rw [abs_of_nonneg (sub_nonneg.mpr hty), max_eq_left (sub_nonneg.mpr hty)]; ring
  · rw [abs_of_neg (sub_neg.mpr hty), max_eq_right (by linarith)]; ring

private lemma potential_sub_neg_asymp {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) (t : ℝ) :
    MartOT.Var.potential μ t - (mean μ - mass μ * t) = 2 * ∫ y, max (t - y) 0 ∂μ := by
  have := hμ.1
  have hlin : ∫ y, (y - t) ∂μ = mean μ - mass μ * t := by
    rw [integral_sub hμ.2 (integrable_const t), integral_const, smul_eq_mul]
    simp [mass, mean, Measure.real_def, mul_comm]
  have hsub_int : Integrable (fun y : ℝ => y - t) μ := hμ.2.sub (integrable_const t)
  rw [MartOT.Var.potential, ← hlin,
    ← integral_sub (inM_integrable_abs_sub hμ t) hsub_int,
    ← integral_const_mul]
  congr 1; ext y
  rcases le_or_gt y t with hyt | hyt
  · rw [abs_of_nonpos (sub_nonpos.mpr hyt), max_eq_left (sub_nonneg.mpr hyt)]; ring
  · rw [abs_of_pos (sub_pos.mpr hyt), max_eq_right (by linarith)]; ring

private lemma potential_tendsto_top {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun t => MartOT.Var.potential μ t - (mass μ * t - mean μ)) atTop (𝓝 0) := by
  simp_rw [potential_sub_pos_asymp hμ]
  have hlim : Tendsto (fun t => ∫ y, max (y - t) 0 ∂μ) atTop (𝓝 (∫ _y, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|) ?_ ?_ hμ.2.abs ?_
    · exact Eventually.of_forall fun t => by fun_prop
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self y]) (abs_nonneg y)
    · refine ae_of_all _ fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop y] with t ht
      symm
      exact max_eq_right (sub_nonpos.mpr ht)
  simpa using hlim.const_mul 2

private lemma potential_tendsto_bot {μ : Measure ℝ} (hμ : MartOT.Var.InM μ) :
    Tendsto (fun t => MartOT.Var.potential μ t - (mean μ - mass μ * t)) atBot (𝓝 0) := by
  simp_rw [potential_sub_neg_asymp hμ]
  have hlim : Tendsto (fun t => ∫ y, max (t - y) 0 ∂μ) atBot (𝓝 (∫ _y, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|) ?_ ?_ hμ.2.abs ?_
    · exact Eventually.of_forall fun t => by fun_prop
    · filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_le_abs y]) (abs_nonneg y)
    · refine ae_of_all _ fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_le_atBot y] with t ht
      symm
      exact max_eq_right (sub_nonpos.mpr ht)
  simpa using hlim.const_mul 2

private lemma inM_of_le {μ ν : Measure ℝ} (hν : MartOT.Var.InM ν) (hle : μ ≤ ν) :
    MartOT.Var.InM μ := by
  have := hν.1
  exact ⟨isFiniteMeasure_of_le ν hle, hν.2.mono_measure hle⟩

private lemma potential_add {μ₁ μ₂ : Measure ℝ} (h₁ : MartOT.Var.InM μ₁)
    (h₂ : MartOT.Var.InM μ₂) (x : ℝ) :
    MartOT.Var.potential (μ₁ + μ₂) x = MartOT.Var.potential μ₁ x + MartOT.Var.potential μ₂ x := by
  simp only [MartOT.Var.potential]
  exact integral_add_measure (inM_integrable_abs_sub h₁ x) (inM_integrable_abs_sub h₂ x)

private lemma mass_add {μ₁ μ₂ : Measure ℝ} (h₁ : MartOT.Var.InM μ₁) (h₂ : MartOT.Var.InM μ₂) :
    mass (μ₁ + μ₂) = mass μ₁ + mass μ₂ := by
  have := h₁.1; have := h₂.1
  simp only [mass, Measure.add_apply]
  exact ENNReal.toReal_add (measure_ne_top μ₁ _) (measure_ne_top μ₂ _)

private lemma mean_add {μ₁ μ₂ : Measure ℝ} (h₁ : MartOT.Var.InM μ₁) (h₂ : MartOT.Var.InM μ₂) :
    mean (μ₁ + μ₂) = mean μ₁ + mean μ₂ :=
  integral_add_measure h₁.2 h₂.2

/-! ### Section 3: Reconstructing a measure in 𝓜 from a convex function with linear asymptotes -/

private lemma rderiv_tendsto_top_of_asymp {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {m b : ℝ}
    (hTop : Tendsto (fun t => f t - (m * t - b)) atTop (𝓝 0)) :
    Tendsto (rderiv f) atTop (𝓝 m) := by
  have hslope : ∀ x, Tendsto (fun y => (f y - f x) / (y - x)) atTop (𝓝 m) := by
    intro x
    have h1 : Tendsto (fun y => (f y - (m * y - b)) / (y - x)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun y : ℝ => (y - x)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.atTop_add tendsto_const_nhds)
      simpa [div_eq_mul_inv] using hTop.mul hinv
    have h2 : Tendsto (fun y => (m * x - b - f x) / (y - x)) atTop (𝓝 0) := by
      have hinv : Tendsto (fun y : ℝ => (y - x)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_id.atTop_add tendsto_const_nhds)
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have h3 : Tendsto (fun y => m + (f y - (m * y - b)) / (y - x) +
        (m * x - b - f x) / (y - x)) atTop (𝓝 m) := by
      simpa using (tendsto_const_nhds.add h1).add h2
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop x] with y hy
    have hne : y - x ≠ 0 := (sub_pos.mpr hy).ne'
    field_simp
    ring
  have hle : ∀ x, rderiv f x ≤ m := fun x => by
    refine ge_of_tendsto (hslope x) ?_
    filter_upwards [eventually_gt_atTop x] with y hy
    simpa [slope_def_field] using convex_rderiv_le_slope hf hy
  have hbdd : BddAbove (range (rderiv f)) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hle x⟩
  have hlim : Tendsto (rderiv f) atTop (𝓝 (⨆ x, rderiv f x)) :=
    tendsto_atTop_ciSup (convex_monotone_rderiv hf) hbdd
  have hsup_le : (⨆ x, rderiv f x) ≤ m := ciSup_le hle
  have hm_le : m ≤ ⨆ x, rderiv f x := by
    refine le_of_tendsto (hslope 0) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have h1 : (f y - f 0) / (y - 0) ≤ rderiv f y := by
      simpa [slope_def_field] using
        (convex_slope_le_lderiv hf hy).trans (convex_lderiv_le_rderiv hf y)
    exact h1.trans (le_ciSup hbdd y)
  rw [le_antisymm hsup_le hm_le] at hlim
  exact hlim

private lemma rderiv_tendsto_bot_of_asymp {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {m b : ℝ}
    (hBot : Tendsto (fun t => f t - (b - m * t)) atBot (𝓝 0)) :
    Tendsto (rderiv f) atBot (𝓝 (-m)) := by
  have hslope : ∀ x, Tendsto (fun y => (f x - f y) / (x - y)) atBot (𝓝 (-m)) := by
    intro x
    have hinv : Tendsto (fun y : ℝ => (x - y)⁻¹) atBot (𝓝 0) := by
      have : Tendsto (fun y : ℝ => x - y) atBot atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_const_nhds (x := x)).add_atTop tendsto_neg_atBot_atTop
      exact tendsto_inv_atTop_zero.comp this
    have h1 : Tendsto (fun y => (f y - (b - m * y)) / (x - y)) atBot (𝓝 0) := by
      simpa [div_eq_mul_inv] using hBot.mul hinv
    have h2 : Tendsto (fun y => (f x - (b - m * x)) / (x - y)) atBot (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have h3 : Tendsto (fun y => -m - (f y - (b - m * y)) / (x - y) +
        (f x - (b - m * x)) / (x - y)) atBot (𝓝 (-m)) := by
      simpa using (tendsto_const_nhds.sub h1).add h2
    refine h3.congr' ?_
    filter_upwards [eventually_lt_atBot x] with y hy
    have hne : x - y ≠ 0 := (sub_pos.mpr hy).ne'
    field_simp
    ring
  have hge : ∀ x, -m ≤ rderiv f x := fun x => by
    refine le_of_tendsto (hslope x) ?_
    filter_upwards [eventually_lt_atBot x] with y hy
    have h1 := (convex_slope_le_lderiv hf hy).trans (convex_lderiv_le_rderiv hf x)
    rw [slope_def_field] at h1
    exact h1
  have hbdd : BddBelow (range (rderiv f)) := ⟨-m, by rintro _ ⟨x, rfl⟩; exact hge x⟩
  have hlim : Tendsto (rderiv f) atBot (𝓝 (⨅ x, rderiv f x)) :=
    tendsto_atBot_ciInf (convex_monotone_rderiv hf) hbdd
  have hle_inf : -m ≤ ⨅ x, rderiv f x := le_ciInf hge
  have hinf_le : ⨅ x, rderiv f x ≤ -m := by
    refine ge_of_tendsto (hslope 0) ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
    have h1 : rderiv f y ≤ (f 0 - f y) / (0 - y) := by
      simpa [slope_def_field] using convex_rderiv_le_slope hf hy
    exact (ciInf_le hbdd y).trans h1
  rw [le_antisymm hinf_le hle_inf] at hlim
  exact hlim

private lemma measure_from_convex_asymp {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) {m b : ℝ}
    (hm : 0 ≤ m)
    (hTop : Tendsto (fun t => f t - (m * t - b)) atTop (𝓝 0))
    (hBot : Tendsto (fun t => f t - (b - m * t)) atBot (𝓝 0)) :
    let θ := (convexHalfStieltjes hf).measure
    MartOT.Var.InM θ ∧ mass θ = m ∧ mean θ = b ∧ ∀ x, MartOT.Var.potential θ x = f x := by
  intro θ
  set D := convexHalfStieltjes hf
  have hD_fun : (D : ℝ → ℝ) = fun a => rderiv f a / 2 := funext (convexHalfStieltjes_apply hf)
  have hD_top : Tendsto D atTop (𝓝 (m / 2)) := by
    rw [hD_fun]
    exact (rderiv_tendsto_top_of_asymp hf hTop).div_const 2
  have hD_bot : Tendsto D atBot (𝓝 (-m / 2)) := by
    rw [hD_fun]
    exact (rderiv_tendsto_bot_of_asymp hf hBot).div_const 2
  have hfin : IsFiniteMeasure θ := D.isFiniteMeasure hD_bot hD_top
  have huniv : θ univ = ENNReal.ofReal m := by
    rw [D.measure_univ hD_bot hD_top]
    congr 1; ring
  have hmass : mass θ = m := by
    simp [mass, huniv, ENNReal.toReal_ofReal hm]
  have hIoi : ∀ t, θ (Ioi t) = ENNReal.ofReal ((m - rderiv f t) / 2) := fun t => by
    rw [D.measure_Ioi hD_top t, convexHalfStieltjes_apply]
    congr 1; ring
  have hIic : ∀ t, θ (Iic t) = ENNReal.ofReal ((rderiv f t + m) / 2) := fun t => by
    rw [D.measure_Iic hD_bot t, convexHalfStieltjes_apply]
    congr 1; ring
  have hrderiv_le : ∀ t, rderiv f t ≤ m := fun t =>
    (convex_monotone_rderiv hf).ge_of_tendsto (rderiv_tendsto_top_of_asymp hf hTop) t
  have hrderiv_ge : ∀ t, -m ≤ rderiv f t := fun t =>
    (convex_monotone_rderiv hf).le_of_tendsto (rderiv_tendsto_bot_of_asymp hf hBot) t
  -- Right tail moment via Tonelli + FTC
  have hpos_mom : ∀ x, ∫⁻ y, ENNReal.ofReal (max (y - x) 0) ∂θ =
      ENNReal.ofReal ((f x - (m * x - b)) / 2) := fun x => by
    let A : Set (ℝ × ℝ) := {p | x < p.2 ∧ p.2 < p.1}
    have hA : MeasurableSet A :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst)
    have hswap1 : ∫⁻ y, ENNReal.ofReal (max (y - x) 0) ∂θ =
        ∫⁻ y, ∫⁻ t, A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t) ∂volume ∂θ := by
      congr 1; ext y
      have hsec : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) =
          (Ioo x y).indicator (fun _ => (1 : ℝ≥0∞)) := by
        ext t; by_cases ht : x < t ∧ t < y <;> simp [A, ht]
      rw [hsec, lintegral_indicator measurableSet_Ioo, setLIntegral_one, Real.volume_Ioo]
      rcases le_or_gt x y with hxy | hxy
      · rw [max_eq_left (sub_nonneg.mpr hxy)]
      · rw [max_eq_right (by linarith), ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr (by linarith)]
    have hmeasA : AEMeasurable (Function.uncurry fun y t => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t))
        (θ.prod volume) := (measurable_const.indicator hA).aemeasurable
    rw [hswap1, lintegral_lintegral_swap hmeasA]
    have hswap2 : ∫⁻ t, ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t) ∂θ ∂volume =
        ∫⁻ t in Ioi x, θ (Ioi t) ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioi]
      congr 1; ext t
      by_cases ht : t ∈ Ioi x
      · rw [indicator_of_mem ht]
        have ht' : x < t := mem_Ioi.mp ht
        have hsec : (fun y => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) =
            (Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext y; by_cases hy : t < y <;> simp [A, ht', hy]
        rw [hsec, lintegral_indicator measurableSet_Ioi, setLIntegral_one]
      · rw [indicator_of_notMem ht]
        have ht' : ¬ x < t := ht
        have hzero : (fun y => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) = fun _ => 0 := by
          ext y; simp [A, ht']
        rw [hzero, lintegral_zero]
    rw [hswap2]
    have hIoi_sup : ∫⁻ t in Ioi x, θ (Ioi t) ∂volume =
        ⨆ n : ℕ, ∫⁻ t in Ioc x (x + (n : ℝ)), θ (Ioi t) ∂volume := by
      have hmeas_g : Measurable (fun t : ℝ => θ (Ioi t)) :=
        Antitone.measurable fun a b hab => measure_mono (Ioi_subset_Ioi hab)
      have hInd : (Ioi x).indicator (fun t => θ (Ioi t)) =
          fun t => ⨆ n : ℕ, (Ioc x (x + (n : ℝ))).indicator (fun t => θ (Ioi t)) t := by
        ext t
        by_cases ht : t ∈ Ioi x
        · rw [indicator_of_mem ht]
          obtain ⟨n₀, hn₀⟩ := exists_nat_gt (t - x)
          refine le_antisymm ?_ (iSup_le fun n => indicator_le_self _ _ t)
          calc θ (Ioi t) = (Ioc x (x + (n₀ : ℝ))).indicator (fun t => θ (Ioi t)) t := by
                rw [indicator_of_mem (show t ∈ Ioc x (x + (n₀ : ℝ)) from ⟨mem_Ioi.mp ht, by linarith⟩)]
            _ ≤ ⨆ n : ℕ, (Ioc x (x + (n : ℝ))).indicator (fun t => θ (Ioi t)) t :=
                le_iSup (fun n : ℕ => (Ioc x (x + (n : ℝ))).indicator (fun t => θ (Ioi t)) t) n₀
        · rw [indicator_of_notMem ht]
          symm
          exact le_antisymm (iSup_le fun n => by rw [indicator_of_notMem (fun hmem => ht hmem.1)]) bot_le
      rw [← lintegral_indicator measurableSet_Ioi, hInd,
        lintegral_iSup (fun n => hmeas_g.indicator measurableSet_Ioc)
          (fun i j hij t => indicator_le_indicator_of_subset
            (Ioc_subset_Ioc_right (by gcongr)) (fun _ => bot_le) t)]
      congr 1; ext n
      exact lintegral_indicator measurableSet_Ioc _
    rw [hIoi_sup]
    have hval : ∀ n : ℕ, ∫⁻ t in Ioc x (x + (n : ℝ)), θ (Ioi t) ∂volume =
        ENNReal.ofReal ((f x - (m * x - b) - (f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b))) / 2) := by
      intro n
      simp_rw [hIoi]
      have hle : x ≤ x + (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hint : IntegrableOn (fun t => (m - rderiv f t) / 2) (Ioc x (x + (n : ℝ))) volume := by
        have h1 := (convex_monotone_rderiv hf).intervalIntegrable (μ := volume) (a := x) (b := x + (n : ℝ))
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at h1
        exact ((integrableOn_const (by simp [Real.volume_Ioc])).sub h1).div_const 2
      have hnn : ∀ᵐ t ∂(volume.restrict (Ioc x (x + (n : ℝ)))), 0 ≤ (m - rderiv f t) / 2 :=
        ae_of_all _ fun t => div_nonneg (sub_nonneg.mpr (hrderiv_le t)) (by norm_num)
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      rw [← intervalIntegral.integral_of_le hle, intervalIntegral.integral_div,
        intervalIntegral.integral_sub intervalIntegrable_const
          (convex_monotone_rderiv hf).intervalIntegrable,
        convex_ftc hf hle, intervalIntegral.integral_const, smul_eq_mul]
      ring
    simp_rw [hval]
    have hmono : Monotone (fun n : ℕ =>
        ENNReal.ofReal ((f x - (m * x - b) - (f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b))) / 2)) := by
      intro i j hij
      dsimp only
      rw [← hval i, ← hval j]
      exact lintegral_mono_set (Ioc_subset_Ioc_right (by gcongr))
    have htend : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((f x - (m * x - b) - (f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b))) / 2))
        atTop (𝓝 (ENNReal.ofReal ((f x - (m * x - b)) / 2))) := by
      have h1 : Tendsto (fun n : ℕ => f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b)) atTop (𝓝 0) :=
        hTop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
      exact ENNReal.tendsto_ofReal (by simpa using ((tendsto_const_nhds.sub h1).div_const 2))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) htend
  -- Left tail moment via Tonelli + FTC
  have hneg_mom : ∀ x, ∫⁻ y, ENNReal.ofReal (max (x - y) 0) ∂θ =
      ENNReal.ofReal ((f x - (b - m * x)) / 2) := fun x => by
    let A : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ x}
    have hA : MeasurableSet A :=
      (measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hswap1 : ∫⁻ y, ENNReal.ofReal (max (x - y) 0) ∂θ =
        ∫⁻ y, ∫⁻ t, A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t) ∂volume ∂θ := by
      congr 1; ext y
      have hsec : (fun t => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) =
          (Icc y x).indicator (fun _ => (1 : ℝ≥0∞)) := by
        ext t; by_cases ht : y ≤ t ∧ t ≤ x <;> simp [A, ht]
      rw [hsec, lintegral_indicator measurableSet_Icc, setLIntegral_one, Real.volume_Icc]
      rcases le_or_gt y x with hyx | hyx
      · rw [max_eq_left (sub_nonneg.mpr hyx)]
      · rw [max_eq_right (by linarith), ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero.mpr (by linarith)]
    have hmeasA : AEMeasurable (Function.uncurry fun y t => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t))
        (θ.prod volume) := (measurable_const.indicator hA).aemeasurable
    rw [hswap1, lintegral_lintegral_swap hmeasA]
    have hswap2 : ∫⁻ t, ∫⁻ y, A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t) ∂θ ∂volume =
        ∫⁻ t in Iic x, θ (Iic t) ∂volume := by
      rw [← lintegral_indicator measurableSet_Iic]
      congr 1; ext t
      by_cases ht : t ∈ Iic x
      · rw [indicator_of_mem ht]
        have ht' : t ≤ x := mem_Iic.mp ht
        have hsec : (fun y => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) =
            (Iic t).indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext y; by_cases hy : y ≤ t <;> simp [A, ht', hy]
        rw [hsec, lintegral_indicator measurableSet_Iic, setLIntegral_one]
      · rw [indicator_of_notMem ht]
        have ht' : ¬ t ≤ x := ht
        have hzero : (fun y => A.indicator (fun _ => (1 : ℝ≥0∞)) (y, t)) = fun _ => 0 := by
          ext y; simp [A, ht']
        rw [hzero, lintegral_zero]
    rw [hswap2]
    have hIic_sup : ∫⁻ t in Iic x, θ (Iic t) ∂volume =
        ⨆ n : ℕ, ∫⁻ t in Ioc (x - (n : ℝ)) x, θ (Iic t) ∂volume := by
      have hmeas_g : Measurable (fun t : ℝ => θ (Iic t)) :=
        Monotone.measurable fun a b hab => measure_mono (Iic_subset_Iic.mpr hab)
      have hInd : (Iic x).indicator (fun t => θ (Iic t)) =
          fun t => ⨆ n : ℕ, (Ioc (x - (n : ℝ)) x).indicator (fun t => θ (Iic t)) t := by
        ext t
        by_cases ht : t ∈ Iic x
        · rw [indicator_of_mem ht]
          obtain ⟨n₀, hn₀⟩ := exists_nat_gt (x - t)
          refine le_antisymm ?_ (iSup_le fun n => indicator_le_self _ _ t)
          calc θ (Iic t) = (Ioc (x - (n₀ : ℝ)) x).indicator (fun t => θ (Iic t)) t := by
                rw [indicator_of_mem (show t ∈ Ioc (x - (n₀ : ℝ)) x from ⟨by linarith, mem_Iic.mp ht⟩)]
            _ ≤ ⨆ n : ℕ, (Ioc (x - (n : ℝ)) x).indicator (fun t => θ (Iic t)) t :=
                le_iSup (fun n : ℕ => (Ioc (x - (n : ℝ)) x).indicator (fun t => θ (Iic t)) t) n₀
        · rw [indicator_of_notMem ht]
          symm
          exact le_antisymm (iSup_le fun n => by rw [indicator_of_notMem (fun hmem => ht hmem.2)]) bot_le
      rw [← lintegral_indicator measurableSet_Iic, hInd,
        lintegral_iSup (fun n => hmeas_g.indicator measurableSet_Ioc)
          (fun i j hij t => indicator_le_indicator_of_subset
            (Ioc_subset_Ioc_left (by gcongr)) (fun _ => bot_le) t)]
      congr 1; ext n
      exact lintegral_indicator measurableSet_Ioc _
    rw [hIic_sup]
    have hval : ∀ n : ℕ, ∫⁻ t in Ioc (x - (n : ℝ)) x, θ (Iic t) ∂volume =
        ENNReal.ofReal ((f x - (b - m * x) - (f (x - (n : ℝ)) - (b - m * (x - (n : ℝ))))) / 2) := by
      intro n
      simp_rw [hIic]
      have hle : x - (n : ℝ) ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hint : IntegrableOn (fun t => (rderiv f t + m) / 2) (Ioc (x - (n : ℝ)) x) volume := by
        have h1 := (convex_monotone_rderiv hf).intervalIntegrable (μ := volume) (a := x - (n : ℝ)) (b := x)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at h1
        exact (h1.add (integrableOn_const (by simp [Real.volume_Ioc]))).div_const 2
      have hnn : ∀ᵐ t ∂(volume.restrict (Ioc (x - (n : ℝ)) x)), 0 ≤ (rderiv f t + m) / 2 :=
        ae_of_all _ fun t => div_nonneg (by linarith [hrderiv_ge t]) (by norm_num)
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
      congr 1
      rw [← intervalIntegral.integral_of_le hle, intervalIntegral.integral_div,
        intervalIntegral.integral_add
          (convex_monotone_rderiv hf).intervalIntegrable intervalIntegrable_const,
        convex_ftc hf hle, intervalIntegral.integral_const, smul_eq_mul]
      ring
    simp_rw [hval]
    have hmono : Monotone (fun n : ℕ =>
        ENNReal.ofReal ((f x - (b - m * x) - (f (x - (n : ℝ)) - (b - m * (x - (n : ℝ))))) / 2)) := by
      intro i j hij
      dsimp only
      rw [← hval i, ← hval j]
      exact lintegral_mono_set (Ioc_subset_Ioc_left (by gcongr))
    have htend : Tendsto (fun n : ℕ =>
        ENNReal.ofReal ((f x - (b - m * x) - (f (x - (n : ℝ)) - (b - m * (x - (n : ℝ))))) / 2))
        atTop (𝓝 (ENNReal.ofReal ((f x - (b - m * x)) / 2))) := by
      have hsub_bot : Tendsto (fun n : ℕ => x - (n : ℝ)) atTop atBot := by
        simpa [sub_eq_add_neg] using tendsto_const_nhds.add_atBot
          (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      have h1 : Tendsto (fun n : ℕ => f (x - (n : ℝ)) - (b - m * (x - (n : ℝ)))) atTop (𝓝 0) :=
        hBot.comp hsub_bot
      exact ENNReal.tendsto_ofReal (by simpa using ((tendsto_const_nhds.sub h1).div_const 2))
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) htend
  -- Nonnegativity of f x - (m x - b) and f x - (b - m x)
  have hf_ge_top : ∀ x, m * x - b ≤ f x := fun x => by
    have h1 : ∀ n : ℕ, 0 ≤ f x - (m * x - b) - (f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b)) := by
      intro n
      have hle : x ≤ x + (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hftc : f (x + (n : ℝ)) - f x ≤ m * (n : ℝ) := by
        rw [← convex_ftc hf hle]
        calc ∫ t in x..(x + (n : ℝ)), rderiv f t
            ≤ ∫ _ in x..(x + (n : ℝ)), m :=
              intervalIntegral.integral_mono_on hle (convex_monotone_rderiv hf).intervalIntegrable
                intervalIntegrable_const (fun t _ => hrderiv_le t)
          _ = m * (n : ℝ) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      linarith
    have hlim : Tendsto (fun n : ℕ => f x - (m * x - b) -
        (f (x + (n : ℝ)) - (m * (x + (n : ℝ)) - b))) atTop (𝓝 (f x - (m * x - b))) := by
      simpa using tendsto_const_nhds.sub
        (hTop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop))
    linarith [ge_of_tendsto' hlim h1]
  have hf_ge_bot : ∀ x, b - m * x ≤ f x := fun x => by
    have h1 : ∀ n : ℕ, 0 ≤ f x - (b - m * x) - (f (x - (n : ℝ)) - (b - m * (x - (n : ℝ)))) := by
      intro n
      have hle : x - (n : ℝ) ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hftc : -(m * (n : ℝ)) ≤ f x - f (x - (n : ℝ)) := by
        rw [← convex_ftc hf hle]
        calc -(m * (n : ℝ))
            = ∫ _ in (x - (n : ℝ))..x, (-m) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          _ ≤ ∫ t in (x - (n : ℝ))..x, rderiv f t :=
              intervalIntegral.integral_mono_on hle intervalIntegrable_const
                (convex_monotone_rderiv hf).intervalIntegrable (fun t _ => hrderiv_ge t)
      linarith
    have hsub_bot : Tendsto (fun n : ℕ => x - (n : ℝ)) atTop atBot := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.add_atBot
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    have hlim : Tendsto (fun n : ℕ => f x - (b - m * x) -
        (f (x - (n : ℝ)) - (b - m * (x - (n : ℝ))))) atTop (𝓝 (f x - (b - m * x))) := by
      simpa using tendsto_const_nhds.sub (hBot.comp hsub_bot)
    linarith [ge_of_tendsto' hlim h1]
  have hf_nn : ∀ x, 0 ≤ f x := fun x => by linarith [hf_ge_top x, hf_ge_bot x]
  -- Combine to get InM θ, mean θ = b, potential θ = f
  have hlint_abs : ∀ x, ∫⁻ y, ENNReal.ofReal |y - x| ∂θ = ENNReal.ofReal (f x) := fun x => by
    have heq : ∀ y, ENNReal.ofReal |y - x| =
        ENNReal.ofReal (max (y - x) 0) + ENNReal.ofReal (max (x - y) 0) := fun y => by
      rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
      congr 1
      rcases le_or_gt x y with hxy | hxy
      · rw [abs_of_nonneg (sub_nonneg.mpr hxy), max_eq_left (sub_nonneg.mpr hxy),
          max_eq_right (by linarith), add_zero]
      · rw [abs_of_neg (sub_neg.mpr hxy), max_eq_right (by linarith),
          max_eq_left (sub_nonneg.mpr hxy.le), zero_add]; ring
    simp_rw [heq]
    rw [lintegral_add_left (by fun_prop), hpos_mom x, hneg_mom x,
      ← ENNReal.ofReal_add (div_nonneg (sub_nonneg.mpr (hf_ge_top x)) (by norm_num))
        (div_nonneg (sub_nonneg.mpr (hf_ge_bot x)) (by norm_num))]
    congr 1; ring
  have hint_id : Integrable (fun y : ℝ => y) θ := by
    refine ⟨aestronglyMeasurable_id, ?_⟩
    rw [HasFiniteIntegral]
    have h0 := hlint_abs 0
    simp only [sub_zero] at h0
    have : ∀ y : ℝ, ‖y‖ₑ = ENNReal.ofReal |y| := fun y => by
      rw [Real.enorm_eq_ofReal_abs]
    simp_rw [this, h0]
    exact ENNReal.ofReal_lt_top
  have hInM : MartOT.Var.InM θ := ⟨hfin, hint_id⟩
  have hpot : ∀ x, MartOT.Var.potential θ x = f x := fun x => by
    have h1 := ofReal_integral_eq_lintegral_ofReal (inM_integrable_abs_sub hInM x)
      (ae_of_all _ fun y => abs_nonneg (y - x))
    rw [hlint_abs x] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun y => abs_nonneg _) (hf_nn x)).mp h1
  have hmean : mean θ = b := by
    have hp := ofReal_integral_eq_lintegral_ofReal (inM_integrable_pos_sub hInM 0)
      (ae_of_all _ fun y => le_max_right _ _)
    rw [hpos_mom 0] at hp
    have hp_eq : ∫ y, max (y - 0) 0 ∂θ = (f 0 - (m * 0 - b)) / 2 :=
      (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)
        (div_nonneg (sub_nonneg.mpr (hf_ge_top 0)) (by norm_num))).mp hp
    have hn := ofReal_integral_eq_lintegral_ofReal (inM_integrable_sub_pos hInM 0)
      (ae_of_all _ fun y => le_max_right _ _)
    rw [hneg_mom 0] at hn
    have hn_eq : ∫ y, max (0 - y) 0 ∂θ = (f 0 - (b - m * 0)) / 2 :=
      (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)
        (div_nonneg (sub_nonneg.mpr (hf_ge_bot 0)) (by norm_num))).mp hn
    have hsplit : mean θ = (∫ y, max (y - 0) 0 ∂θ) - ∫ y, max (0 - y) 0 ∂θ := by
      simp only [mean]
      rw [← integral_sub (inM_integrable_pos_sub hInM 0) (inM_integrable_sub_pos hInM 0)]
      congr 1; ext y
      rcases le_or_gt 0 y with hy | hy
      · simp [max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]
      · simp [max_eq_right hy.le, max_eq_left (neg_nonneg.mpr hy.le)]
    rw [hsplit, hp_eq, hn_eq]
    ring
  exact ⟨hInM, hmass, hmean, hpot⟩

/-! ### Section 4: `integralE`, `ConvexLE`, and `ExtConvexLE` via potentials -/

private lemma integralE_eq_of_integrable {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ) :
    MartOT.Var.integralE μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  simp only [MartOT.Var.integralE, ModelRiskOT.Duality.extIntegral]
  have h1 : ∀ x : ℝ, ((f x : EReal)).toENNReal = ENNReal.ofReal (f x) := fun x => rfl
  have h2 : ∀ x : ℝ, (-(f x : EReal)).toENNReal = ENNReal.ofReal (-f x) := fun x => by
    rw [← EReal.coe_neg]; rfl
  simp_rw [h1, h2]
  have hp_lt : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ := by
    calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ
        ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := lintegral_mono fun x => by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ < ⊤ := hf.2
  have hn_lt : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ < ⊤ := by
    calc ∫⁻ x, ENNReal.ofReal (-f x) ∂μ
        ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := lintegral_mono fun x => by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
      _ < ⊤ := hf.2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, EReal.coe_sub,
    ← EReal.coe_ennreal_toReal hp_lt.ne, ← EReal.coe_ennreal_toReal hn_lt.ne]

private lemma integralE_of_nonneg {μ : Measure ℝ} {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  simp only [MartOT.Var.integralE, ModelRiskOT.Duality.extIntegral]
  have h1 : ∀ x : ℝ, ((f x : EReal)).toENNReal = ENNReal.ofReal (f x) := fun _ => rfl
  have h2 : ∀ x : ℝ, (-(f x : EReal)).toENNReal = 0 := fun x => by
    rw [← EReal.coe_neg]
    exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hf x))
  simp_rw [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

private lemma integralE_add_integrable {μ : Measure ℝ} {ψ ℓ : ℝ → ℝ}
    (hψ_nn : ∀ y, 0 ≤ ψ y) (hψ_meas : Measurable ψ) (hℓ : Integrable ℓ μ) :
    MartOT.Var.integralE μ (fun y => ψ y + ℓ y) =
      ((∫⁻ y, ENNReal.ofReal (ψ y) ∂μ : ENNReal) : EReal) + ((∫ y, ℓ y ∂μ : ℝ) : EReal) := by
  by_cases hfin : ∫⁻ y, ENNReal.ofReal (ψ y) ∂μ < ⊤
  · have hψ_int : Integrable ψ μ := by
      refine ⟨hψ_meas.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have : ∀ y, ‖ψ y‖ₑ = ENNReal.ofReal (ψ y) := fun y => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hψ_nn y)]
      simp_rw [this]
      exact hfin
    have hsum_int : Integrable (fun y => ψ y + ℓ y) μ := hψ_int.add hℓ
    rw [integralE_eq_of_integrable hsum_int, integral_add hψ_int hℓ, EReal.coe_add,
      ← ofReal_integral_eq_lintegral_ofReal hψ_int (ae_of_all _ hψ_nn),
      EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg hψ_nn)]
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, EReal.coe_ennreal_top, EReal.top_add_coe]
    simp only [MartOT.Var.integralE, ModelRiskOT.Duality.extIntegral]
    have h1 : ∀ y : ℝ, (((ψ y + ℓ y : ℝ) : EReal)).toENNReal = ENNReal.ofReal (ψ y + ℓ y) := fun _ => rfl
    have h2 : ∀ y : ℝ, (-((ψ y + ℓ y : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-(ψ y + ℓ y)) := fun y => by
      rw [← EReal.coe_neg]; rfl
    simp_rw [h1, h2]
    have hneg_lt : ∫⁻ y, ENNReal.ofReal (-(ψ y + ℓ y)) ∂μ < ⊤ := by
      calc ∫⁻ y, ENNReal.ofReal (-(ψ y + ℓ y)) ∂μ
          ≤ ∫⁻ y, ‖ℓ y‖ₑ ∂μ := lintegral_mono fun y => by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (by linarith [hψ_nn y, neg_le_abs (ℓ y)])
        _ < ⊤ := hℓ.2
    have hpos_top : ∫⁻ y, ENNReal.ofReal (ψ y + ℓ y) ∂μ = ⊤ := by
      have hneg_ℓ : ∫⁻ y, ENNReal.ofReal (-ℓ y) ∂μ < ⊤ := by
        calc ∫⁻ y, ENNReal.ofReal (-ℓ y) ∂μ
            ≤ ∫⁻ y, ‖ℓ y‖ₑ ∂μ := lintegral_mono fun y => by
              rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
          _ < ⊤ := hℓ.2
      have hle : ∫⁻ y, ENNReal.ofReal (ψ y) ∂μ ≤
          (∫⁻ y, ENNReal.ofReal (ψ y + ℓ y) ∂μ) + ∫⁻ y, ENNReal.ofReal (-ℓ y) ∂μ := by
        have hadd_m : AEMeasurable (fun y => ENNReal.ofReal (ψ y + ℓ y)) μ :=
          (hψ_meas.aemeasurable.add hℓ.aemeasurable).ennreal_ofReal
        rw [← lintegral_add_left' hadd_m]
        refine lintegral_mono fun y => ?_
        calc ENNReal.ofReal (ψ y)
            = ENNReal.ofReal ((ψ y + ℓ y) + (-ℓ y)) := by ring_nf
          _ ≤ ENNReal.ofReal (ψ y + ℓ y) + ENNReal.ofReal (-ℓ y) := ENNReal.ofReal_add_le
      rw [hfin] at hle
      by_contra hne
      exact not_le_of_gt (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, hneg_ℓ⟩) hle
    rw [hpos_top, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hneg_lt.ne]
    exact EReal.top_sub_coe _

private lemma convexLE_implies_potentials {μ η : Measure ℝ} (h : MartOT.Var.ConvexLE μ η) :
    mass μ = mass η ∧ mean μ = mean η ∧ ∀ x, MartOT.Var.potential μ x ≤ MartOT.Var.potential η x := by
  have hμ := h.1; have hη := h.2.1; have := hμ.1; have := hη.1
  have hle_int : ∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ → Integrable φ μ → Integrable φ η →
      ∫ y, φ y ∂μ ≤ ∫ y, φ y ∂η := fun φ hφ h1 h2 => by
    have := h.2.2 φ hφ
    rw [integralE_eq_of_integrable h1, integralE_eq_of_integrable h2, EReal.coe_le_coe_iff] at this
    exact this
  have hmass_le : mass μ ≤ mass η := by
    have := hle_int (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ)
      (integrable_const 1) (integrable_const 1)
    simpa [mass, Measure.real_def] using this
  have hmass_ge : mass η ≤ mass μ := by
    have := hle_int (fun _ => (-1 : ℝ)) (convexOn_const (-1) convex_univ)
      (integrable_const (-1)) (integrable_const (-1))
    simp only [integral_const, smul_eq_mul, mul_neg, mul_one, neg_le_neg_iff, Measure.real_def] at this
    exact this
  have hmean_le : mean μ ≤ mean η :=
    hle_int id (convexOn_id convex_univ) hμ.2 hη.2
  have hmean_ge : mean η ≤ mean μ := by
    have := hle_int (fun y => -y) ((concaveOn_id convex_univ).neg) hμ.2.neg hη.2.neg
    rw [integral_neg, integral_neg, neg_le_neg_iff] at this
    exact this
  refine ⟨le_antisymm hmass_le hmass_ge, le_antisymm hmean_le hmean_ge, fun x => ?_⟩
  have habs_conv : ConvexOn ℝ univ (fun y : ℝ => |y - x|) := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hEq : (a * u + b * v) - x = a * (u - x) + b * (v - x) := by
      calc (a * u + b * v) - x = (a * u + b * v) - (a + b) * x := by rw [hab, one_mul]
        _ = a * (u - x) + b * (v - x) := by ring
    rw [hEq]
    calc |a * (u - x) + b * (v - x)|
        ≤ |a * (u - x)| + |b * (v - x)| := abs_add_le _ _
      _ = a * |u - x| + b * |v - x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  exact hle_int (fun y => |y - x|) habs_conv (inM_integrable_abs_sub hμ x) (inM_integrable_abs_sub hη x)

private lemma convexLE_of_potentials {μ η : Measure ℝ} (hμ : MartOT.Var.InM μ)
    (hη : MartOT.Var.InM η) (hmass : mass μ = mass η) (hmean : mean μ = mean η)
    (hpot : ∀ x, MartOT.Var.potential μ x ≤ MartOT.Var.potential η x) :
    MartOT.Var.ConvexLE μ η := by
  refine ⟨hμ, hη, fun φ hφ => ?_⟩
  have := hμ.1; have := hη.1
  let ψ : ℝ → ℝ := fun y => φ y - φ 0 - rderiv φ 0 * y
  let ℓ : ℝ → ℝ := fun y => φ 0 + rderiv φ 0 * y
  have hφ_eq : φ = fun y => ψ y + ℓ y := by ext y; dsimp only [ψ, ℓ]; ring
  have hψ_nn : ∀ y, 0 ≤ ψ y := fun y => by
    have := convex_subgradient_rderiv hφ 0 y
    simp only [sub_zero] at this
    simp only [ψ]; linarith
  have hψ_meas : Measurable ψ :=
    (((convex_continuous hφ).sub continuous_const).sub (continuous_const.mul continuous_id)).measurable
  have hℓ_μ : Integrable ℓ μ := (integrable_const (φ 0)).add (hμ.2.const_mul (rderiv φ 0))
  have hℓ_η : Integrable ℓ η := (integrable_const (φ 0)).add (hη.2.const_mul (rderiv φ 0))
  have hℓ_eq : ∫ y, ℓ y ∂μ = ∫ y, ℓ y ∂η := by
    simp only [ℓ]
    rw [integral_add (integrable_const _) (hμ.2.const_mul _),
      integral_add (integrable_const _) (hη.2.const_mul _),
      integral_const, integral_const, integral_const_mul, integral_const_mul,
      smul_eq_mul, smul_eq_mul]
    change mass μ * φ 0 + rderiv φ 0 * mean μ = mass η * φ 0 + rderiv φ 0 * mean η
    rw [hmass, hmean]
  rw [hφ_eq, integralE_add_integrable hψ_nn hψ_meas hℓ_μ,
    integralE_add_integrable hψ_nn hψ_meas hℓ_η, hℓ_eq]
  refine add_le_add ?_ le_rfl
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  set σ : Measure ℝ := (convexStieltjes hφ).measure
  have : SigmaFinite σ := stieltjes_sigmaFinite (convexStieltjes hφ)
  have hrepr : ∀ y, ENNReal.ofReal (ψ y) =
      (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂σ) +
      (∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂σ) := fun y => convex_repr hφ y
  simp_rw [hrepr]
  have hm1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (max (p.1 - p.2) 0)) := by fun_prop
  have hm2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (max (p.2 - p.1) 0)) := by fun_prop
  rw [lintegral_add_left (Measurable.lintegral_prod_right' hm1),
    lintegral_add_left (Measurable.lintegral_prod_right' hm1)]
  refine add_le_add ?_ ?_
  · calc ∫⁻ y, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂σ ∂μ
        = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y, ENNReal.ofReal (max (y - s) 0) ∂μ ∂σ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ ≤ ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y, ENNReal.ofReal (max (y - s) 0) ∂η ∂σ :=
          lintegral_mono fun s => by
            rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_pos_sub hμ s)
              (ae_of_all _ fun _ => le_max_right _ _),
              ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_pos_sub hη s)
              (ae_of_all _ fun _ => le_max_right _ _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := potential_sub_pos_asymp hμ s
            have h2 := potential_sub_pos_asymp hη s
            rw [hmass, hmean] at h1
            linarith [hpot s]
      _ = ∫⁻ y, ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max (y - s) 0) ∂σ ∂η :=
          (lintegral_lintegral_swap hm1.aemeasurable).symm
  · calc ∫⁻ y, ∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂σ ∂μ
        = ∫⁻ s in Iic (0 : ℝ), ∫⁻ y, ENNReal.ofReal (max (s - y) 0) ∂μ ∂σ :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ ≤ ∫⁻ s in Iic (0 : ℝ), ∫⁻ y, ENNReal.ofReal (max (s - y) 0) ∂η ∂σ :=
          lintegral_mono fun s => by
            rw [← ofReal_integral_eq_lintegral_ofReal (inM_integrable_sub_pos hμ s)
              (ae_of_all _ fun _ => le_max_right _ _),
              ← ofReal_integral_eq_lintegral_ofReal (inM_integrable_sub_pos hη s)
              (ae_of_all _ fun _ => le_max_right _ _)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := potential_sub_neg_asymp hμ s
            have h2 := potential_sub_neg_asymp hη s
            rw [hmass, hmean] at h1
            linarith [hpot s]
      _ = ∫⁻ y, ∫⁻ s in Iic (0 : ℝ), ENNReal.ofReal (max (s - y) 0) ∂σ ∂η :=
          (lintegral_lintegral_swap hm2.aemeasurable).symm

private lemma extConvexLE_of_convexLE {η θ : Measure ℝ} (h : MartOT.Var.ConvexLE η θ) :
    MartOT.Var.ExtConvexLE η θ := by
  refine ⟨h.1, h.2.1, fun φ hφ hnn => ?_⟩
  have := h.2.2 φ hφ
  rw [integralE_of_nonneg hnn, integralE_of_nonneg hnn, EReal.coe_ennreal_le_coe_ennreal_iff] at this
  exact this

private lemma extConvexLE_of_le {θ η' : Measure ℝ} (hη' : MartOT.Var.InM η') (hle : θ ≤ η') :
    MartOT.Var.ExtConvexLE θ η' :=
  ⟨inM_of_le hη' hle, hη', fun _ _ _ => lintegral_mono' hle le_rfl⟩

private lemma extConvexLE_trans {μ η η' : Measure ℝ} (h1 : MartOT.Var.ExtConvexLE μ η)
    (h2 : MartOT.Var.ExtConvexLE η η') : MartOT.Var.ExtConvexLE μ η' :=
  ⟨h1.1, h2.2.1, fun φ hφ hnn => (h1.2.2 φ hφ hnn).trans (h2.2.2 φ hφ hnn)⟩

/-! ### Section 5: The greatest convex minorant `hHat` of `u_ν - u_μ` -/

private lemma convexOn_max_sub (t : ℝ) : ConvexOn ℝ univ (fun y : ℝ => max (y - t) 0) :=
  ((convexOn_id convex_univ).sub (concaveOn_const t convex_univ)).sup (convexOn_const 0 convex_univ)

private lemma convexOn_sub_max (t : ℝ) : ConvexOn ℝ univ (fun y : ℝ => max (t - y) 0) :=
  ((convexOn_const t convex_univ).sub (concaveOn_id convex_univ)).sup (convexOn_const 0 convex_univ)

private lemma extConvexLE_bounds {μ ν : Measure ℝ} (hμν : MartOT.Var.ExtConvexLE μ ν) :
    0 ≤ mass ν - mass μ ∧
    (∀ t, 0 ≤ MartOT.Var.potential ν t - MartOT.Var.potential μ t) ∧
    (∀ t, (mass ν - mass μ) * t - (mean ν - mean μ) ≤
      MartOT.Var.potential ν t - MartOT.Var.potential μ t) ∧
    (∀ t, (mean ν - mean μ) - (mass ν - mass μ) * t ≤
      MartOT.Var.potential ν t - MartOT.Var.potential μ t) := by
  have hμ := hμν.1; have hν := hμν.2.1; have := hμ.1; have := hν.1
  have hle_int : ∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ → (∀ y, 0 ≤ φ y) →
      Integrable φ μ → Integrable φ ν → ∫ y, φ y ∂μ ≤ ∫ y, φ y ∂ν := fun φ hφ hnn h1 h2 => by
    have h := hμν.2.2 φ hφ hnn
    rw [← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ hnn),
      ← ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ hnn)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hnn)).mp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hle_int (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ) (fun _ => zero_le_one)
      (integrable_const 1) (integrable_const 1)
    simp only [integral_const, smul_eq_mul, mul_one] at this
    exact sub_nonneg.mpr this
  · intro t
    have habs_conv : ConvexOn ℝ univ (fun y : ℝ => |y - t|) := by
      have : (fun y : ℝ => |y - t|) = fun y => max (y - t) 0 + max (t - y) 0 := by
        ext y
        rcases le_or_gt t y with hty | hty
        · rw [abs_of_nonneg (sub_nonneg.mpr hty), max_eq_left (sub_nonneg.mpr hty),
            max_eq_right (by linarith), add_zero]
        · rw [abs_of_neg (sub_neg.mpr hty), max_eq_right (by linarith),
            max_eq_left (sub_nonneg.mpr hty.le), zero_add]; ring
      rw [this]
      exact (convexOn_max_sub t).add (convexOn_sub_max t)
    exact sub_nonneg.mpr (hle_int _ habs_conv (fun y => abs_nonneg _)
      (inM_integrable_abs_sub hμ t) (inM_integrable_abs_sub hν t))
  · intro t
    have h1 := hle_int _ (convexOn_max_sub t) (fun _ => le_max_right _ _)
      (inM_integrable_pos_sub hμ t) (inM_integrable_pos_sub hν t)
    have hpμ := potential_sub_pos_asymp hμ t
    have hpν := potential_sub_pos_asymp hν t
    linarith
  · intro t
    have h1 := hle_int _ (convexOn_sub_max t) (fun _ => le_max_right _ _)
      (inM_integrable_sub_pos hμ t) (inM_integrable_sub_pos hν t)
    have hnμ := potential_sub_neg_asymp hμ t
    have hnν := potential_sub_neg_asymp hν t
    linarith

private noncomputable def affMinorants (h : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | ∀ t, p.1 * t + p.2 ≤ h t}

private noncomputable def convexMinorant (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ p ∈ affMinorants h, v = p.1 * x + p.2}

private lemma convexMinorant_nonempty {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) (x : ℝ) :
    {v : ℝ | ∃ p ∈ affMinorants h, v = p.1 * x + p.2}.Nonempty :=
  ⟨0, (0, 0), fun t => by simpa using h0 t, by simp⟩

private lemma convexMinorant_bddAbove (h : ℝ → ℝ) (x : ℝ) :
    BddAbove {v : ℝ | ∃ p ∈ affMinorants h, v = p.1 * x + p.2} :=
  ⟨h x, by rintro _ ⟨p, hp, rfl⟩; exact hp x⟩

private lemma convexMinorant_le {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) (x : ℝ) :
    convexMinorant h x ≤ h x :=
  csSup_le (convexMinorant_nonempty h0 x) (by rintro _ ⟨p, hp, rfl⟩; exact hp x)

private lemma aff_le_convexMinorant {h : ℝ → ℝ} {a c : ℝ} (hac : ∀ t, a * t + c ≤ h t) (x : ℝ) :
    a * x + c ≤ convexMinorant h x :=
  le_csSup (convexMinorant_bddAbove h x) ⟨(a, c), hac, rfl⟩

private lemma convexMinorant_convex {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) :
    ConvexOn ℝ univ (convexMinorant h) := by
  refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  refine csSup_le (convexMinorant_nonempty h0 _) ?_
  rintro _ ⟨p, hp, rfl⟩
  have h1 : p.1 * x + p.2 ≤ convexMinorant h x := aff_le_convexMinorant hp x
  have h2 : p.1 * y + p.2 ≤ convexMinorant h y := aff_le_convexMinorant hp y
  calc p.1 * (α * x + β * y) + p.2
      = α * (p.1 * x + p.2) + β * (p.1 * y + p.2) := by
        calc p.1 * (α * x + β * y) + p.2
            = p.1 * (α * x + β * y) + (α + β) * p.2 := by rw [hαβ, one_mul]
          _ = α * (p.1 * x + p.2) + β * (p.1 * y + p.2) := by ring
    _ ≤ α * convexMinorant h x + β * convexMinorant h y :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hα) (mul_le_mul_of_nonneg_left h2 hβ)

private lemma le_convexMinorant_of_convex {h g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hle : ∀ t, g t ≤ h t) (x : ℝ) : g x ≤ convexMinorant h x := by
  have haff : ∀ t, rderiv g x * t + (g x - rderiv g x * x) ≤ h t := fun t => by
    have := convex_subgradient_rderiv hg x t
    linarith [hle t]
  have h1 := aff_le_convexMinorant haff x
  linarith

private lemma convexMinorant_affine_on_Icc {h : ℝ → ℝ} (hcont : Continuous h)
    (h0 : ∀ t, 0 ≤ h t) {c d : ℝ} (hcd : c < d)
    (hU : ∀ t ∈ Icc c d, convexMinorant h t < h t) :
    ∀ t ∈ Icc c d,
      convexMinorant h t = convexMinorant h c + slope (convexMinorant h) c d * (t - c) := by
  set hHat := convexMinorant h
  have hhConv : ConvexOn ℝ univ hHat := convexMinorant_convex h0
  have hhCont : Continuous hHat := convex_continuous hhConv
  set m : ℝ := slope hHat c d
  let ℓ : ℝ → ℝ := fun t => hHat c + m * (t - c)
  have hle_on : ∀ t ∈ Icc c d, hHat t ≤ ℓ t := fun t ht => by
    set s : ℝ := (t - c) / (d - c)
    have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hcd).le
    have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hcd)).mpr (sub_le_sub_right ht.2 c)
    have ht_eq : t = (1 - s) * c + s * d := by
      have hne : d - c ≠ 0 := (sub_pos.mpr hcd).ne'
      simp only [s]; field_simp; ring
    have hℓ_eq : ℓ t = (1 - s) * hHat c + s * hHat d := by
      have hne : d - c ≠ 0 := (sub_pos.mpr hcd).ne'
      simp only [ℓ, m, slope_def_field, s]; field_simp; ring
    rw [hℓ_eq]
    calc hHat t = hHat ((1 - s) * c + s * d) := by rw [ht_eq]
      _ ≤ (1 - s) * hHat c + s * hHat d := hhConv.2 (mem_univ c) (mem_univ d) (sub_nonneg.mpr hs1) hs0 (by ring)
  have hge_off : ∀ t, t ∉ Icc c d → ℓ t ≤ hHat t := fun t ht => by
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with htc | hdt
    · have hmono := hhConv.slope_mono (mem_univ c) ⟨mem_univ t, htc.ne⟩ ⟨mem_univ d, hcd.ne'⟩ (htc.trans hcd).le
      rw [slope_def_field] at hmono
      have hmul := mul_le_mul_of_nonpos_right hmono (sub_neg.mpr htc).le
      rw [div_mul_cancel₀ _ (sub_neg.mpr htc).ne] at hmul
      simp only [ℓ, m]; linarith
    · have hmono := hhConv.slope_mono (mem_univ c) ⟨mem_univ d, hcd.ne'⟩ ⟨mem_univ t, (hcd.trans hdt).ne'⟩ hdt.le
      simp only [slope_def_field] at hmono
      have hmul := mul_le_mul_of_nonneg_right hmono (sub_pos.mpr (hcd.trans hdt)).le
      rw [div_mul_cancel₀ _ (sub_pos.mpr (hcd.trans hdt)).ne'] at hmul
      simp only [ℓ, m, slope_def_field]; linarith
  intro x₀ hx₀
  refine le_antisymm (hle_on x₀ hx₀) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hcd.le) (hcont.sub hhCont).continuousOn
  set δ : ℝ := h xmin - hHat xmin
  have hδ : 0 < δ := sub_pos.mpr (hU xmin hxmin_mem)
  have hℓCont : Continuous ℓ := continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hcd.le) (hℓCont.sub hhCont).continuousOn
  set M : ℝ := ℓ xmax - hHat xmax
  have hM : 0 ≤ M := sub_nonneg.mpr (hle_on xmax hxmax_mem)
  set θ : ℝ := min (1 / 2) (δ / (M + 1))
  have hθ_pos : 0 < θ := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hθ_le1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθM : θ * M ≤ δ := by
    calc θ * M ≤ (δ / (M + 1)) * M := mul_le_mul_of_nonneg_right (min_le_right _ _) hM
      _ ≤ (δ / (M + 1)) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ.le (by linarith))
      _ = δ := div_mul_cancel₀ _ (by linarith)
  let g : ℝ → ℝ := fun t => max (hHat t) ((1 - θ) * hHat t + θ * ℓ t)
  have hℓConv : ConvexOn ℝ univ ℓ := by
    refine ⟨convex_univ, fun u _ v _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul, ℓ]
    have : a * (hHat c + m * (u - c)) + b * (hHat c + m * (v - c)) =
        (a + b) * hHat c + m * (a * u + b * v - (a + b) * c) := by ring
    rw [this, hab, one_mul, one_mul]
  have hgConv : ConvexOn ℝ univ g := by
    have hcomb : ConvexOn ℝ univ (fun t => (1 - θ) * hHat t + θ * ℓ t) :=
      (hhConv.smul (sub_nonneg.mpr hθ_le1)).add (hℓConv.smul hθ_pos.le)
    exact hhConv.sup hcomb
  have hg_le : ∀ t, g t ≤ h t := fun t => by
    refine max_le (convexMinorant_le h0 t) ?_
    by_cases ht : t ∈ Icc c d
    · have h1 : ℓ t - hHat t ≤ M := hxmax ht
      have h2 : δ ≤ h t - hHat t := hxmin ht
      have h3 : θ * (ℓ t - hHat t) ≤ δ := (mul_le_mul_of_nonneg_left h1 hθ_pos.le).trans hθM
      linarith
    · have h1 : ℓ t ≤ hHat t := hge_off t ht
      have h2 : hHat t ≤ h t := convexMinorant_le h0 t
      nlinarith
  have hcontra := le_convexMinorant_of_convex hgConv hg_le x₀
  have hgt : hHat x₀ < g x₀ := lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
  linarith

private lemma convexMinorant_rderiv_eq_lderiv_on_gap {h : ℝ → ℝ} (hcont : Continuous h)
    (h0 : ∀ t, 0 ≤ h t) {p q : ℝ} (hpq : p < q)
    (hU : ∀ t ∈ Ioo p q, convexMinorant h t < h t) :
    rderiv (convexMinorant h) p = lderiv (convexMinorant h) q := by
  set hHat := convexMinorant h
  have hhConv : ConvexOn ℝ univ hHat := convexMinorant_convex h0
  have hhCont : Continuous hHat := convex_continuous hhConv
  have hconst : ∀ x ∈ Ioo p q, ∀ y ∈ Ioo p q, rderiv hHat x = rderiv hHat y := by
    intro x hx y hy
    wlog hxy : x ≤ y generalizing x y
    · exact (this y hy x hx (le_of_not_ge hxy)).symm
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · rfl
    obtain ⟨d, hyd, hdq⟩ := exists_between hy.2
    have hIcc : ∀ t ∈ Icc x d, hHat t < h t := fun t ht => hU t ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hdq⟩
    have haff := convexMinorant_affine_on_Icc hcont h0 (hlt.trans hyd) hIcc
    set m := slope hHat x d
    have hr : ∀ z ∈ Ico x d, rderiv hHat z = m := fun z hz => by
      have hderiv : HasDerivWithinAt hHat m (Ioi z) z := by
        have hlin : HasDerivWithinAt (fun t => hHat x + m * (t - x)) m (Ioi z) z := by
          simpa using ((hasDerivWithinAt_id z (Ioi z)).sub_const x).const_mul m |>.const_add (hHat x)
        refine hlin.congr_of_eventuallyEq ?_ (haff z ⟨hz.1, hz.2.le⟩)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hz.2)] with t ht1 ht2
        exact haff t ⟨hz.1.trans ht1.le, ht2.le⟩
      exact hderiv.derivWithin (uniqueDiffWithinAt_Ioi z)
    rw [hr x ⟨le_rfl, hlt.trans hyd⟩, hr y ⟨hlt.le, hyd⟩]
  obtain ⟨x₀, hx₀p, hx₀q⟩ := exists_between hpq
  set M := rderiv hHat x₀
  have hM : ∀ x ∈ Ioo p q, rderiv hHat x = M := fun x hx => hconst x hx x₀ ⟨hx₀p, hx₀q⟩
  have hp_eq : rderiv hHat p = M := by
    have hrc := (convex_rderiv_rightContinuous hhConv p).mono_left
      (nhdsWithin_mono p Ioi_subset_Ici_self)
    have hev : ∀ᶠ x in 𝓝[>] p, rderiv hHat x = M := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpq)] with x hx1 hx2
      exact hM x ⟨hx1, hx2⟩
    exact tendsto_nhds_unique hrc (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  have hq_ge : M ≤ lderiv hHat q := by
    rw [← hM x₀ ⟨hx₀p, hx₀q⟩]
    exact convex_rderiv_le_lderiv_of_lt hhConv hx₀q
  have hq_le : lderiv hHat q ≤ M := by
    have hslope_le : ∀ r ∈ Ioo p q, slope hHat r q ≤ M := fun r hr => by
      have ht : Tendsto (fun x => slope hHat r x) (𝓝[<] q) (𝓝 (slope hHat r q)) := by
        have hcont_s : ContinuousAt (fun x => (hHat x - hHat r) / (x - r)) q :=
          ((hhCont.continuousAt.sub continuousAt_const).div
            (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hr.2.ne'))
        simpa [slope_def_field] using hcont_s.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hr.2)] with x hx1 hx2
      have hrx : r < x := hx2
      have hx_mem : x ∈ Ioo p q := ⟨hr.1.trans hrx, hx1⟩
      calc slope hHat r x ≤ lderiv hHat x := convex_slope_le_lderiv hhConv hrx
        _ ≤ rderiv hHat x := convex_lderiv_le_rderiv hhConv x
        _ = M := hM x hx_mem
    have hderiv_l := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp
      (convex_hasDerivWithinAt_lderiv hhConv q)
    refine le_of_tendsto hderiv_l ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpq)] with r hr1 hr2
    rw [slope_comm]
    exact hslope_le r ⟨hr2, hr1⟩
  rw [hp_eq]
  exact le_antisymm hq_ge hq_le

private lemma convexMinorant_rderiv_eq_on_Ioc_gap {h : ℝ → ℝ} (hcont : Continuous h)
    (h0 : ∀ t, 0 ≤ h t) {p q : ℝ} (hpq : p < q)
    (hU : ∀ t ∈ Ioc p q, convexMinorant h t < h t) :
    rderiv (convexMinorant h) p = rderiv (convexMinorant h) q := by
  have hhConv := convexMinorant_convex h0
  have hhCont := convex_continuous hhConv
  have hopen : IsOpen {t | convexMinorant h t < h t} := isOpen_lt hhCont hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen q (hU q ⟨hpq, le_rfl⟩)
  have hgap : ∀ t ∈ Ioo p (q + ε), convexMinorant h t < h t := fun t ht => by
    by_cases htq : t ≤ q
    · exact hU t ⟨ht.1, htq⟩
    · push Not at htq
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr htq)]
      linarith [ht.2]
  have h1 := convexMinorant_rderiv_eq_lderiv_on_gap hcont h0 (by linarith) hgap
  have h2 : rderiv (convexMinorant h) p ≤ rderiv (convexMinorant h) q :=
    convex_monotone_rderiv hhConv hpq.le
  have h3 : rderiv (convexMinorant h) q ≤ lderiv (convexMinorant h) (q + ε) :=
    convex_rderiv_le_lderiv_of_lt hhConv (by linarith)
  linarith

private lemma contact_rderiv_le {u_ν u_μ : ℝ → ℝ} (hν : ConvexOn ℝ univ u_ν)
    (hμ : ConvexOn ℝ univ u_μ) (h0 : ∀ t, 0 ≤ u_ν t - u_μ t) {t : ℝ}
    (ht : convexMinorant (fun x => u_ν x - u_μ x) t = u_ν t - u_μ t) :
    rderiv (convexMinorant (fun x => u_ν x - u_μ x)) t ≤ rderiv u_ν t - rderiv u_μ t := by
  set h := fun x => u_ν x - u_μ x
  set hHat := convexMinorant h
  have hhConv := convexMinorant_convex h0
  have hd1 := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (convex_hasDerivWithinAt_rderiv hhConv t)
  have hd2 := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
    ((convex_hasDerivWithinAt_rderiv hν t).sub (convex_hasDerivWithinAt_rderiv hμ t))
  refine le_of_tendsto_of_tendsto hd1 hd2 ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : t < x)
  rw [slope_def_field, slope_def_field]
  have hle : hHat x ≤ h x := convexMinorant_le h0 x
  refine div_le_div_of_nonneg_right ?_ (sub_pos.mpr hx).le
  dsimp only [Pi.sub_apply, h, hHat] at hle ht ⊢
  linarith

private lemma contact_lderiv_ge {u_ν u_μ : ℝ → ℝ} (hν : ConvexOn ℝ univ u_ν)
    (hμ : ConvexOn ℝ univ u_μ) (h0 : ∀ t, 0 ≤ u_ν t - u_μ t) {t : ℝ}
    (ht : convexMinorant (fun x => u_ν x - u_μ x) t = u_ν t - u_μ t) :
    lderiv u_ν t - lderiv u_μ t ≤ lderiv (convexMinorant (fun x => u_ν x - u_μ x)) t := by
  set h := fun x => u_ν x - u_μ x
  set hHat := convexMinorant h
  have hhConv := convexMinorant_convex h0
  have hd1 := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp (convex_hasDerivWithinAt_lderiv hhConv t)
  have hd2 := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp
    ((convex_hasDerivWithinAt_lderiv hν t).sub (convex_hasDerivWithinAt_lderiv hμ t))
  refine le_of_tendsto_of_tendsto hd2 hd1 ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : x < t)
  rw [slope_def_field, slope_def_field]
  have hle : hHat x ≤ h x := convexMinorant_le h0 x
  have hpos : 0 < t - x := sub_pos.mpr hx
  have hrew : ∀ a b : ℝ, (a - b) / (x - t) = (b - a) / (t - x) := fun a b => by
    have : x - t = -(t - x) := by ring
    rw [this, div_neg, ← neg_div, neg_sub]
  rw [hrew, hrew]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  dsimp only [Pi.sub_apply, h, hHat] at hle ht ⊢
  linarith

private lemma convexMinorant_rderiv_sub_le {u_ν u_μ : ℝ → ℝ} (hν : ConvexOn ℝ univ u_ν)
    (hμ : ConvexOn ℝ univ u_μ) (h0 : ∀ t, 0 ≤ u_ν t - u_μ t) {a b : ℝ} (hab : a ≤ b) :
    rderiv (convexMinorant (fun x => u_ν x - u_μ x)) b -
      rderiv (convexMinorant (fun x => u_ν x - u_μ x)) a ≤
    rderiv u_ν b - rderiv u_ν a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  set h := fun x => u_ν x - u_μ x
  set hHat := convexMinorant h
  have hhConv := convexMinorant_convex h0
  have hcont : Continuous h := (convex_continuous hν).sub (convex_continuous hμ)
  have hhCont : Continuous hHat := convex_continuous hhConv
  let K : Set ℝ := {t | hHat t = h t}
  have hK_closed : IsClosed K := isClosed_eq hhCont hcont
  let S : Set ℝ := Ioc a b ∩ K
  by_cases hS : S.Nonempty
  · set t₂ : ℝ := sSup S
    have hS_bdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
    have ht₂_le : t₂ ≤ b := csSup_le hS (fun t ht => ht.1.2)
    have ht₂_gt : a < t₂ := by
      obtain ⟨s, hs⟩ := hS
      exact lt_of_lt_of_le hs.1.1 (le_csSup hS_bdd hs)
    have ht₂_mem : t₂ ∈ K :=
      hK_closed.closure_subset_iff.mpr (fun t ht => ht.2) (csSup_mem_closure hS hS_bdd)
    have hr_b : rderiv hHat b = rderiv hHat t₂ := by
      rcases eq_or_lt_of_le ht₂_le with ht₂_eq | ht₂_lt
      · rw [ht₂_eq]
      · symm
        refine convexMinorant_rderiv_eq_on_Ioc_gap hcont h0 ht₂_lt fun t ht => ?_
        have hle := convexMinorant_le h0 t
        refine lt_of_le_of_ne hle fun heq => ?_
        have hmem : t ∈ S := ⟨⟨ht₂_gt.trans ht.1, ht.2⟩, heq⟩
        exact (not_lt.mpr (le_csSup hS_bdd hmem)) ht.1
    have hpair : ∀ s ∈ S, s ≤ t₂ →
        rderiv hHat t₂ - lderiv hHat s ≤ rderiv u_ν b - rderiv u_ν a := fun s hs hst₂ => by
      have h1 := contact_rderiv_le hν hμ h0 ht₂_mem
      have h2 := contact_lderiv_ge hν hμ h0 hs.2
      have h3 : lderiv u_μ s ≤ rderiv u_μ t₂ :=
        (convex_lderiv_le_rderiv hμ s).trans (convex_monotone_rderiv hμ hst₂)
      have h4 : rderiv u_ν t₂ ≤ rderiv u_ν b := convex_monotone_rderiv hν ht₂_le
      have h5 : rderiv u_ν a ≤ lderiv u_ν s := convex_rderiv_le_lderiv_of_lt hν hs.1.1
      linarith
    set t₁ : ℝ := sInf S
    have hS_bddB : BddBelow S := ⟨a, fun t ht => ht.1.1.le⟩
    have ht₁_ge : a ≤ t₁ := le_csInf hS (fun t ht => ht.1.1.le)
    have ht₁_le : t₁ ≤ t₂ := by
      obtain ⟨s, hs⟩ := hS
      exact (csInf_le hS_bddB hs).trans (le_csSup hS_bdd hs)
    rcases eq_or_lt_of_le ht₁_ge with ht₁_eq | ht₁_gt
    · -- Subcase 2b: t₁ = a
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hrc := Metric.continuousWithinAt_iff.mp (convex_rderiv_rightContinuous hhConv a) ε hε
      obtain ⟨δ, hδ, hball⟩ := hrc
      have hlt_inf : t₁ < a + δ := by linarith
      obtain ⟨s, hs, hs_lt⟩ := exists_lt_of_csInf_lt hS hlt_inf
      have hdist : dist s a < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hs.1.1)]
        linarith
      have hclose := hball hs.1.1.le hdist
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (convex_monotone_rderiv hhConv hs.1.1.le))] at hclose
      have hp := hpair s hs (le_csSup hS_bdd hs)
      have hlr := convex_lderiv_le_rderiv hhConv s
      rw [hr_b]
      linarith
    · -- Subcase 2a: a < t₁
      have ht₁_mem : t₁ ∈ K :=
        hK_closed.closure_subset_iff.mpr (fun t ht => ht.2) (csInf_mem_closure hS hS_bddB)
      have hgap : ∀ t ∈ Ioo a t₁, hHat t < h t := fun t ht => by
        refine lt_of_le_of_ne (convexMinorant_le h0 t) fun heq => ?_
        have hmem : t ∈ S := ⟨⟨ht.1, ht.2.le.trans (ht₁_le.trans ht₂_le)⟩, heq⟩
        exact (not_lt.mpr (csInf_le hS_bddB hmem)) ht.2
      have hr_a : rderiv hHat a = lderiv hHat t₁ :=
        convexMinorant_rderiv_eq_lderiv_on_gap hcont h0 ht₁_gt hgap
      have hp : rderiv hHat t₂ - lderiv hHat t₁ ≤ rderiv u_ν b - rderiv u_ν a := by
        have h1 := contact_rderiv_le hν hμ h0 ht₂_mem
        have h2 := contact_lderiv_ge hν hμ h0 ht₁_mem
        have h3 : lderiv u_μ t₁ ≤ rderiv u_μ t₂ :=
          (convex_lderiv_le_rderiv hμ t₁).trans (convex_monotone_rderiv hμ ht₁_le)
        have h4 : rderiv u_ν t₂ ≤ rderiv u_ν b := convex_monotone_rderiv hν ht₂_le
        have h5 : rderiv u_ν a ≤ lderiv u_ν t₁ := convex_rderiv_le_lderiv_of_lt hν ht₁_gt
        linarith
      rw [hr_b, hr_a]
      exact hp
  · -- Case 1: S = ∅
    have hgap : ∀ t ∈ Ioc a b, hHat t < h t := fun t ht => by
      refine lt_of_le_of_ne (convexMinorant_le h0 t) fun heq => ?_
      exact hS ⟨t, ht, heq⟩
    have heq := convexMinorant_rderiv_eq_on_Ioc_gap hcont h0 hlt hgap
    rw [heq, sub_self]
    exact sub_nonneg.mpr (convex_monotone_rderiv hν hab)

/-! ### Section 6: Existence and properties of the shadow -/

private lemma shadow_exists {μ ν : Measure ℝ} (hμν : MartOT.Var.ExtConvexLE μ ν) :
    ∃ η : Measure ℝ, MartOT.Var.IsShadow ν μ η := by
  have hμ := hμν.1; have hν := hμν.2.1
  obtain ⟨hm_nn, hh_nn, hh_top_lb, hh_bot_lb⟩ := extConvexLE_bounds hμν
  set h : ℝ → ℝ := fun x => MartOT.Var.potential ν x - MartOT.Var.potential μ x
  set hHat : ℝ → ℝ := convexMinorant h
  set m : ℝ := mass ν - mass μ
  set b : ℝ := mean ν - mean μ
  have hhConv : ConvexOn ℝ univ hHat := convexMinorant_convex hh_nn
  have hHat_top : Tendsto (fun t => hHat t - (m * t - b)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (potential_tendsto_top hν).sub (potential_tendsto_top hμ))
      (fun t => sub_nonneg.mpr (by
        have := aff_le_convexMinorant (h := h) (a := m) (c := -b) (fun s => by linarith [hh_top_lb s]) t
        linarith))
      (fun t => by
        have := convexMinorant_le hh_nn t
        have : (MartOT.Var.potential ν t - (mass ν * t - mean ν)) -
            (MartOT.Var.potential μ t - (mass μ * t - mean μ)) = h t - (m * t - b) := by
          simp only [h, m, b]; ring
        linarith)
  have hHat_bot : Tendsto (fun t => hHat t - (b - m * t)) atBot (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using (potential_tendsto_bot hν).sub (potential_tendsto_bot hμ))
      (fun t => sub_nonneg.mpr (by
        have := aff_le_convexMinorant (h := h) (a := -m) (c := b) (fun s => by linarith [hh_bot_lb s]) t
        linarith))
      (fun t => by
        have := convexMinorant_le hh_nn t
        have : (MartOT.Var.potential ν t - (mean ν - mass ν * t)) -
            (MartOT.Var.potential μ t - (mean μ - mass μ * t)) = h t - (b - m * t) := by
          simp only [h, m, b]; ring
        linarith)
  obtain ⟨hρ_inM, hρ_mass, hρ_mean, hρ_pot⟩ :=
    measure_from_convex_asymp hhConv hm_nn hHat_top hHat_bot
  set ρ : Measure ℝ := (convexHalfStieltjes hhConv).measure
  let G : StieltjesFunction ℝ := {
    toFun := fun x => (rderiv (MartOT.Var.potential ν) x - rderiv hHat x) / 2
    mono' := fun a c hac => by
      have := convexMinorant_rderiv_sub_le (potential_convex hν) (potential_convex hμ) hh_nn hac
      linarith
    right_continuous' := fun x =>
      ((convex_rderiv_rightContinuous (potential_convex hν) x).sub
        (convex_rderiv_rightContinuous hhConv x)).div_const 2
  }
  set η : Measure ℝ := G.measure
  have hG_add : G + convexHalfStieltjes hhConv = convexHalfStieltjes (potential_convex hν) := by
    ext x
    change (rderiv (MartOT.Var.potential ν) x - rderiv hHat x) / 2 +
      convexHalfStieltjes hhConv x = convexHalfStieltjes (potential_convex hν) x
    rw [convexHalfStieltjes_apply, convexHalfStieltjes_apply]
    ring
  have hsum : η + ρ = ν := by
    rw [← StieltjesFunction.measure_add, hG_add, halfStieltjes_potential_measure hν]
  have hη_le : η ≤ ν := by rw [← hsum]; exact Measure.le_add_right le_rfl
  have hη_inM : MartOT.Var.InM η := inM_of_le hν hη_le
  have hη_mass : mass η = mass μ := by
    have := mass_add hη_inM hρ_inM
    rw [hsum, hρ_mass] at this
    linarith
  have hη_mean : mean η = mean μ := by
    have := mean_add hη_inM hρ_inM
    rw [hsum, hρ_mean] at this
    linarith
  have hη_pot : ∀ x, MartOT.Var.potential η x = MartOT.Var.potential ν x - hHat x := fun x => by
    have := potential_add hη_inM hρ_inM x
    rw [hsum, hρ_pot x] at this
    linarith
  have hμη : MartOT.Var.ConvexLE μ η := by
    refine convexLE_of_potentials hμ hη_inM hη_mass.symm hη_mean.symm fun x => ?_
    rw [hη_pot x]
    have hle := convexMinorant_le hh_nn x
    dsimp only [hHat, h] at hle ⊢
    linarith
  refine ⟨η, hη_le, hμη, fun η' hη'_le hμη' => ?_⟩
  have hη'_inM : MartOT.Var.InM η' := hμη'.2.1
  have := hη'_inM.1
  obtain ⟨hm', hb', hpot'⟩ := convexLE_implies_potentials hμη'
  set ρ' : Measure ℝ := ν - η'
  have hsum' : ρ' + η' = ν := Measure.sub_add_cancel_of_le hη'_le
  have hρ'_inM : MartOT.Var.InM ρ' := inM_of_le hν (by rw [← hsum']; exact Measure.le_add_right le_rfl)
  have hρ'_pot_le : ∀ x, MartOT.Var.potential ρ' x ≤ h x := fun x => by
    have := potential_add hρ'_inM hη'_inM x
    rw [hsum'] at this
    simp only [h]
    linarith [hpot' x]
  have hρ'_le_hHat : ∀ x, MartOT.Var.potential ρ' x ≤ hHat x := fun x =>
    le_convexMinorant_of_convex (potential_convex hρ'_inM) hρ'_pot_le x
  refine convexLE_of_potentials hη_inM hη'_inM (by linarith) (by linarith) fun x => ?_
  have h1 := potential_add hρ'_inM hη'_inM x
  rw [hsum'] at h1
  rw [hη_pot x]
  linarith [hρ'_le_hHat x]

end Helpers

theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ExtConvexLE μ ν) :
    (∃! η : Measure ℝ, MartOT.Var.IsShadow ν μ η) ∧
      ∀ η : Measure ℝ, MartOT.Var.IsShadow ν μ η →
        ∀ η' : Measure ℝ, η' ≤ ν → MartOT.Var.ExtConvexLE μ η' → MartOT.Var.ExtConvexLE η η' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨η, hη⟩ := shadow_exists hμν
    refine ⟨η, hη, fun η' hη' => ?_⟩
    have h1 : MartOT.Var.ConvexLE η η' := hη.2.2 η' hη'.1 hη'.2.1
    have h2 : MartOT.Var.ConvexLE η' η := hη'.2.2 η hη.1 hη.2.1
    obtain ⟨_, _, hp1⟩ := convexLE_implies_potentials h1
    obtain ⟨_, _, hp2⟩ := convexLE_implies_potentials h2
    exact eq_of_potential_eq h2.1 h1.1 fun x => le_antisymm (hp2 x) (hp1 x)
  · intro η hη η' hη'_le hμη'
    obtain ⟨θ, hθ⟩ := shadow_exists hμη'
    have hθ_le_ν : θ ≤ ν := hθ.1.trans hη'_le
    have hηθ : MartOT.Var.ConvexLE η θ := hη.2.2 θ hθ_le_ν hθ.2.1
    exact extConvexLE_trans (extConvexLE_of_convexLE hηθ) (extConvexLE_of_le hμη'.2.1 hθ.1)
