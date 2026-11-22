-- Prove2me | solution 1 for MartOT.Shadow.proposition_4_15
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:09:03.591674+00:00
-- url     : https://prove2.me/submissions/88bebce9-7d8c-4ab2-9e9e-af1348769e2c

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_ConvergesInM

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Prop415Helpers

/-! ### Module 1: `integralE` and basic `ConvexLE` properties -/

lemma toENNReal_coe_real (x : ℝ) : ((x : EReal)).toENNReal = ENNReal.ofReal x := by
  simp [EReal.toENNReal]

lemma toENNReal_neg_coe_real (x : ℝ) : (-(x : EReal)).toENNReal = ENNReal.ofReal (-x) := by
  rw [← EReal.coe_neg, toENNReal_coe_real]

lemma ereal_sub_ennreal_of_ne_top {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  simp [EReal.coe_nnreal_eq_coe_real, EReal.coe_sub]

lemma integralE_eq_of_integrable {α : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f α) :
    MartOT.Var.integralE α f = ((∫ x, f x ∂α : ℝ) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  simp_rw [toENNReal_coe_real, toENNReal_neg_coe_real]
  have hpos_int : Integrable (fun x => max (f x) 0) α := hf.pos_part
  have hneg_int : Integrable (fun x => max (-f x) 0) α := hf.neg.pos_part
  have hpos_fin : ∫⁻ x, ENNReal.ofReal (f x) ∂α ≠ ⊤ := by
    have : (fun x => ENNReal.ofReal (f x)) = (fun x => ENNReal.ofReal (max (f x) 0)) := by
      ext x; simp
    rw [this, ← ofReal_integral_eq_lintegral_ofReal hpos_int (ae_of_all _ fun _ => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top
  have hneg_fin : ∫⁻ x, ENNReal.ofReal (-f x) ∂α ≠ ⊤ := by
    have : (fun x => ENNReal.ofReal (-f x)) = (fun x => ENNReal.ofReal (max (-f x) 0)) := by
      ext x; simp
    rw [this, ← ofReal_integral_eq_lintegral_ofReal hneg_int (ae_of_all _ fun _ => le_max_right _ _)]
    exact ENNReal.ofReal_ne_top
  rw [ereal_sub_ennreal_of_ne_top hpos_fin hneg_fin]
  congr 1
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

lemma integralE_add_integrable {α : Measure ℝ} {ψ a : ℝ → ℝ}
    (hψ_meas : Measurable ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (ha : Integrable a α) :
    MartOT.Var.integralE α (fun x => ψ x + a x) =
      ((∫⁻ x, ENNReal.ofReal (ψ x) ∂α : ℝ≥0∞) : EReal) + ((∫ x, a x ∂α : ℝ) : EReal) := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (ψ x) ∂α < ⊤
  · have hψ_int : Integrable ψ α := by
      refine ⟨hψ_meas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hψ0)]
      exact hfin
    have hsum : Integrable (fun x => ψ x + a x) α := hψ_int.add ha
    rw [integralE_eq_of_integrable hsum, integral_add hψ_int ha, EReal.coe_add]
    congr 1
    rw [← ofReal_integral_eq_lintegral_ofReal hψ_int (ae_of_all _ hψ0)]
    have hnn : 0 ≤ ∫ x, ψ x ∂α := integral_nonneg hψ0
    rw [EReal.coe_ennreal_ofReal, max_eq_left hnn]
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, EReal.coe_ennreal_top, EReal.top_add_coe]
    unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
    simp_rw [toENNReal_coe_real, toENNReal_neg_coe_real]
    have hneg_a : ∫⁻ x, ENNReal.ofReal (-a x) ∂α < ⊤ := by
      have h1 : Integrable (fun x => max (-a x) 0) α := ha.neg.pos_part
      have : (fun x => ENNReal.ofReal (-a x)) = (fun x => ENNReal.ofReal (max (-a x) 0)) := by
        ext x; simp
      rw [this, ← ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun _ => le_max_right _ _)]
      exact ENNReal.ofReal_lt_top
    have hneg_sum : ∫⁻ x, ENNReal.ofReal (-(ψ x + a x)) ∂α < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hneg_a
      linarith [hψ0 x]
    have hpos_top : ∫⁻ x, ENNReal.ofReal (ψ x + a x) ∂α = ⊤ := by
      by_contra hne
      have hlt : ∫⁻ x, ENNReal.ofReal (ψ x + a x) ∂α < ⊤ := lt_top_iff_ne_top.mpr hne
      have hmeas_sum : AEMeasurable (fun x => ENNReal.ofReal (ψ x + a x)) α :=
        ENNReal.measurable_ofReal.comp_aemeasurable (hψ_meas.aemeasurable.add ha.aemeasurable)
      have hle : ∫⁻ x, ENNReal.ofReal (ψ x) ∂α ≤
          ∫⁻ x, ENNReal.ofReal (ψ x + a x) ∂α + ∫⁻ x, ENNReal.ofReal (-a x) ∂α := by
        rw [← lintegral_add_left' hmeas_sum]
        refine lintegral_mono fun x => ?_
        calc ENNReal.ofReal (ψ x) = ENNReal.ofReal ((ψ x + a x) + (-a x)) := by ring_nf
          _ ≤ ENNReal.ofReal (ψ x + a x) + ENNReal.ofReal (-a x) := ENNReal.ofReal_add_le
      rw [hfin] at hle
      exact not_lt_of_ge hle (ENNReal.add_lt_top.mpr ⟨hlt, hneg_a⟩)
    rw [hpos_top, EReal.coe_ennreal_top]
    lift (∫⁻ x, ENNReal.ofReal (-(ψ x + a x)) ∂α) to ℝ≥0 using hneg_sum.ne with c
    simp [EReal.coe_nnreal_eq_coe_real, sub_eq_add_neg]

lemma convexLE_trans {α β γ : Measure ℝ}
    (h1 : MartOT.Var.ConvexLE α β) (h2 : MartOT.Var.ConvexLE β γ) :
    MartOT.Var.ConvexLE α γ :=
  ⟨h1.1, h2.2.1, fun ϕ hϕ => (h1.2.2 ϕ hϕ).trans (h2.2.2 ϕ hϕ)⟩

lemma inM_integrable_abs_sub {α : Measure ℝ} (hα : MartOT.Var.InM α) (x : ℝ) :
    Integrable (fun y : ℝ => |y - x|) α := by
  have : IsFiniteMeasure α := hα.1
  have h1 : Integrable (fun y : ℝ => y - x) α := hα.2.sub (integrable_const x)
  simpa [Real.norm_eq_abs] using h1.norm

lemma convexLE_mass_eq {α β : Measure ℝ} (h : MartOT.Var.ConvexLE α β) :
    α Set.univ = β Set.univ := by
  have : IsFiniteMeasure α := h.1.1
  have : IsFiniteMeasure β := h.2.1.1
  have h1 := h.2.2 (fun _ => (1 : ℝ)) (convexOn_const 1 convex_univ)
  have h2 := h.2.2 (fun _ => (-1 : ℝ)) (convexOn_const (-1) convex_univ)
  rw [integralE_eq_of_integrable (integrable_const _),
      integralE_eq_of_integrable (integrable_const _)] at h1 h2
  simp only [EReal.coe_le_coe_iff, integral_const, smul_eq_mul, mul_one, mul_neg] at h1 h2
  have heq : α.real Set.univ = β.real Set.univ := le_antisymm h1 (by linarith)
  simp only [Measure.real] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top α _) (measure_ne_top β _)).mp heq

lemma convexLE_mean_eq {α β : Measure ℝ} (h : MartOT.Var.ConvexLE α β) :
    ∫ y, y ∂α = ∫ y, y ∂β := by
  have h1 := h.2.2 (fun x : ℝ => x) (convexOn_id convex_univ)
  have h2 := h.2.2 (fun x : ℝ => -x) (concaveOn_id convex_univ).neg
  have hneg1 : Integrable (fun x : ℝ => -x) α := h.1.2.neg
  have hneg2 : Integrable (fun x : ℝ => -x) β := h.2.1.2.neg
  rw [integralE_eq_of_integrable h.1.2, integralE_eq_of_integrable h.2.1.2] at h1
  rw [integralE_eq_of_integrable hneg1, integralE_eq_of_integrable hneg2] at h2
  simp only [EReal.coe_le_coe_iff] at h1 h2
  rw [integral_neg, integral_neg] at h2
  linarith

lemma convexOn_abs_sub (x : ℝ) : ConvexOn ℝ Set.univ (fun y : ℝ => |y - x|) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hkey : a * y₁ + b * y₂ - x = a * (y₁ - x) + b * (y₂ - x) := by
    calc a * y₁ + b * y₂ - x = a * y₁ + b * y₂ - (a + b) * x := by rw [hab, one_mul]
    _ = a * (y₁ - x) + b * (y₂ - x) := by ring
  rw [hkey]
  calc |a * (y₁ - x) + b * (y₂ - x)|
      ≤ |a * (y₁ - x)| + |b * (y₂ - x)| := abs_add_le _ _
    _ = a * |y₁ - x| + b * |y₂ - x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

lemma convexLE_potential_le {α β : Measure ℝ} (h : MartOT.Var.ConvexLE α β) (x : ℝ) :
    MartOT.Var.potential α x ≤ MartOT.Var.potential β x := by
  have h1 := h.2.2 (fun y => |y - x|) (convexOn_abs_sub x)
  rw [integralE_eq_of_integrable (inM_integrable_abs_sub h.1 x),
      integralE_eq_of_integrable (inM_integrable_abs_sub h.2.1 x)] at h1
  exact EReal.coe_le_coe_iff.mp h1

/-! ### Module 2: Right derivative, FTC, and Stieltjes representation of convex functions -/

noncomputable def rderiv (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin u (Set.Ioi x) x

noncomputable def lderiv (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  derivWithin u (Set.Iio x) x

lemma convexOn_continuous {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) : Continuous u :=
  continuousOn_univ.mp (hu.continuousOn isOpen_univ)

lemma convexOn_hasDerivWithinAt_rderiv {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) (x : ℝ) :
    HasDerivWithinAt u (rderiv u x) (Set.Ioi x) x :=
  hu.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)

lemma convexOn_hasDerivWithinAt_lderiv {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) (x : ℝ) :
    HasDerivWithinAt u (lderiv u x) (Set.Iio x) x :=
  hu.hasDerivWithinAt_leftDeriv_of_mem_interior (by simp)

lemma convexOn_monotone_rderiv {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) :
    Monotone (rderiv u) := by
  have h := hu.monotoneOn_rightDeriv
  rw [interior_univ] at h
  intro x y hxy
  exact h trivial trivial hxy

lemma convexOn_rderiv_le_slope {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {x y : ℝ} (hxy : x < y) :
    rderiv u x ≤ slope u x y :=
  hu.rightDeriv_le_slope_of_mem_interior (by simp) trivial hxy

lemma convexOn_slope_le_rderiv {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {x y : ℝ} (hxy : x < y) :
    slope u x y ≤ rderiv u y :=
  (hu.slope_le_leftDeriv_of_mem_interior trivial (by simp) hxy).trans
    (hu.leftDeriv_le_rightDeriv_of_mem_interior (by simp))

lemma convexOn_rderiv_continuousWithinAt {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) (x : ℝ) :
    ContinuousWithinAt (rderiv u) (Set.Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hmono : Monotone (rderiv u) := convexOn_monotone_rderiv hu
  have htend : Tendsto (rderiv u) (𝓝[>] x) (𝓝 (Function.rightLim (rderiv u) x)) :=
    hmono.tendsto_rightLim x
  suffices hL : Function.rightLim (rderiv u) x = rderiv u x by
    rwa [hL] at htend
  refine le_antisymm ?_ ?_
  · have h_le_slope : ∀ y : ℝ, x < y → Function.rightLim (rderiv u) x ≤ slope u x y := by
      intro y hxy
      have hslope_tend : Tendsto (fun t => slope u t y) (𝓝[>] x) (𝓝 (slope u x y)) := by
        simp only [slope_def_field]
        have hcont : ContinuousAt (fun t => (u y - u t) / (y - t)) x :=
          ((continuousAt_const.sub (convexOn_continuous hu).continuousAt).div
            (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hxy.ne'))
        exact hcont.continuousWithinAt
      refine le_of_tendsto_of_tendsto htend hslope_tend ?_
      filter_upwards [Ioo_mem_nhdsGT hxy] with t ht
      exact convexOn_rderiv_le_slope hu ht.2
    have hderiv_tend : Tendsto (slope u x) (𝓝[>] x) (𝓝 (rderiv u x)) :=
      (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (convexOn_hasDerivWithinAt_rderiv hu x)
    refine ge_of_tendsto hderiv_tend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h_le_slope y hy
  · refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hmono (le_of_lt hy)

noncomputable def rderivStieltjes (u : ℝ → ℝ) (hu : ConvexOn ℝ Set.univ u) : StieltjesFunction ℝ where
  toFun := rderiv u
  mono' := convexOn_monotone_rderiv hu
  right_continuous' := convexOn_rderiv_continuousWithinAt hu

lemma convexOn_ftc {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, rderiv u t = u b - u a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (convexOn_continuous hu).continuousOn
    (fun x _ => convexOn_hasDerivWithinAt_rderiv hu x)
    (convexOn_monotone_rderiv hu).intervalIntegrable

lemma convexOn_sub_support_nonneg {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ Set.univ ϕ) (x : ℝ) :
    0 ≤ ϕ x - (ϕ 0 + rderiv ϕ 0 * x) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := convexOn_slope_le_rderiv hϕ hx
    rw [slope_def_field] at h
    have hpos : 0 < 0 - x := by linarith
    have h1 : ϕ 0 - ϕ x ≤ rderiv ϕ 0 * (0 - x) := (div_le_iff₀ hpos).mp h
    linarith
  · simp
  · have h := convexOn_rderiv_le_slope hϕ hx
    rw [slope_def_field] at h
    have h1 : rderiv ϕ 0 * (x - 0) ≤ ϕ x - ϕ 0 := (le_div_iff₀ (by linarith)).mp h
    linarith

lemma convexOn_stieltjes_repr {ϕ : ℝ → ℝ} (hϕ : ConvexOn ℝ Set.univ ϕ) (x : ℝ) :
    ENNReal.ofReal (ϕ x - (ϕ 0 + rderiv ϕ 0 * x)) =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (x - t) 0) ∂(rderivStieltjes ϕ hϕ).measure) +
      (∫⁻ t in Set.Iic (0 : ℝ), ENNReal.ofReal (max (t - x) 0) ∂(rderivStieltjes ϕ hϕ).measure) := by
  set σ : Measure ℝ := (rderivStieltjes ϕ hϕ).measure
  by_cases hx : 0 ≤ x
  · have h2 : ∫⁻ t in Set.Iic (0 : ℝ), ENNReal.ofReal (max (t - x) 0) ∂σ = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ℝ≥0∞)) (fun t ht => by
        have : t - x ≤ 0 := by linarith [mem_Iic.mp ht]
        simp [max_eq_right this]), lintegral_zero]
    rw [h2, add_zero]
    have hinner : ∀ t ∈ Set.Ioi (0 : ℝ),
        ENNReal.ofReal (max (x - t) 0) =
          ∫⁻ s in Set.Ioc (0 : ℝ) x, (Set.Ioc (0 : ℝ) s).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume := by
      intro t ht
      have hset : ∀ s ∈ Set.Ioc (0 : ℝ) x,
          (Set.Ioc (0 : ℝ) s).indicator (fun _ => (1 : ℝ≥0∞)) t =
            (Set.Ici t).indicator (fun _ => (1 : ℝ≥0∞)) s := by
        intro s _
        by_cases hts : t ≤ s
        · simp [Set.indicator_of_mem, mem_Ioc, mem_Ici, mem_Ioi.mp ht, hts]
        · simp [Set.indicator_of_notMem, mem_Ioc, mem_Ici, hts]
      rw [setLIntegral_congr_fun measurableSet_Ioc hset,
          lintegral_indicator measurableSet_Ici, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ici]
      by_cases htx : t ≤ x
      · have : Set.Ici t ∩ Set.Ioc 0 x = Set.Icc t x := by
          ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
          constructor
          · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_lt_of_le (mem_Ioi.mp ht) h1, h2⟩
        rw [this, Real.volume_Icc, max_eq_left (sub_nonneg.mpr htx)]
      · have : Set.Ici t ∩ Set.Ioc 0 x = ∅ := by
          ext s; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
          intro h1 _ h3; linarith
        rw [this, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
    have hmeas : Measurable (Function.uncurry fun t s : ℝ =>
        (Set.Ioc (0 : ℝ) s).indicator (fun _ => (1 : ℝ≥0∞)) t) := by
      have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ p.2} :=
        (measurableSet_lt measurable_const measurable_fst).inter
          (measurableSet_le measurable_fst measurable_snd)
      have heq : (Function.uncurry fun t s : ℝ =>
          (Set.Ioc (0 : ℝ) s).indicator (fun _ => (1 : ℝ≥0∞)) t) =
          Set.indicator {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ p.2} (fun _ => (1 : ℝ≥0∞)) := by
        ext ⟨t, s⟩
        by_cases h : 0 < t ∧ t ≤ s <;> simp [Function.uncurry, Set.indicator, mem_Ioc, h]
      rw [heq]
      exact measurable_const.indicator hS
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hslice : ∀ s ∈ Set.Ioc (0 : ℝ) x,
        (∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) s).indicator (fun _ => (1 : ℝ≥0∞)) t ∂σ) =
          ENNReal.ofReal (rderiv ϕ s - rderiv ϕ 0) := by
      intro s hs
      rw [lintegral_indicator measurableSet_Ioc, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ioc]
      have : Set.Ioc (0 : ℝ) s ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) s :=
        inter_eq_left.mpr Ioc_subset_Ioi_self
      rw [this, StieltjesFunction.measure_Ioc]
      rfl
    rw [setLIntegral_congr_fun measurableSet_Ioc hslice]
    have hint : IntegrableOn (fun s => rderiv ϕ s - rderiv ϕ 0) (Set.Ioc (0 : ℝ) x) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
      exact (convexOn_monotone_rderiv hϕ).intervalIntegrable.sub intervalIntegrable_const
    have hnn : ∀ s ∈ Set.Ioc (0 : ℝ) x, 0 ≤ rderiv ϕ s - rderiv ϕ 0 := fun s hs =>
      sub_nonneg.mpr (convexOn_monotone_rderiv hϕ (le_of_lt hs.1))
    rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hnn)),
        ← intervalIntegral.integral_of_le hx,
        intervalIntegral.integral_sub (convexOn_monotone_rderiv hϕ).intervalIntegrable intervalIntegrable_const,
        convexOn_ftc hϕ hx, intervalIntegral.integral_const, smul_eq_mul]
    congr 1; ring
  · push Not at hx
    have h1 : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (x - t) 0) ∂σ = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ≥0∞)) (fun t ht => by
        have : x - t ≤ 0 := by linarith [mem_Ioi.mp ht]
        simp [max_eq_right this]), lintegral_zero]
    rw [h1, zero_add]
    have hinner : ∀ t ∈ Set.Iic (0 : ℝ),
        ENNReal.ofReal (max (t - x) 0) =
          ∫⁻ s in Set.Ioc x (0 : ℝ), (Set.Ioc s (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t ∂volume := by
      intro t ht
      have hset : ∀ s ∈ Set.Ioc x (0 : ℝ),
          (Set.Ioc s (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t =
            (Set.Iio t).indicator (fun _ => (1 : ℝ≥0∞)) s := by
        intro s _
        by_cases hst : s < t
        · simp [Set.indicator_of_mem, mem_Ioc, mem_Iio, mem_Iic.mp ht, hst]
        · simp [Set.indicator_of_notMem, mem_Ioc, mem_Iio, hst]
      rw [setLIntegral_congr_fun measurableSet_Ioc hset,
          lintegral_indicator measurableSet_Iio, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iio]
      by_cases hxt : x < t
      · have : Set.Iio t ∩ Set.Ioc x 0 = Set.Ioo x t := by
          ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
          constructor
          · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
          · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2.le (mem_Iic.mp ht)⟩
        rw [this, Real.volume_Ioo, max_eq_left (sub_nonneg.mpr hxt.le)]
      · have : Set.Iio t ∩ Set.Ioc x 0 = ∅ := by
          ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2 _; linarith
        rw [this, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun measurableSet_Iic hinner]
    have hmeas : Measurable (Function.uncurry fun t s : ℝ =>
        (Set.Ioc s (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t) := by
      have hS : MeasurableSet {p : ℝ × ℝ | p.2 < p.1 ∧ p.1 ≤ 0} :=
        (measurableSet_lt measurable_snd measurable_fst).inter
          (measurableSet_le measurable_fst measurable_const)
      have heq : (Function.uncurry fun t s : ℝ =>
          (Set.Ioc s (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t) =
          Set.indicator {p : ℝ × ℝ | p.2 < p.1 ∧ p.1 ≤ 0} (fun _ => (1 : ℝ≥0∞)) := by
        ext ⟨t, s⟩
        by_cases h : s < t ∧ t ≤ 0 <;> simp [Function.uncurry, Set.indicator, mem_Ioc, h]
      rw [heq]
      exact measurable_const.indicator hS
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hslice : ∀ s ∈ Set.Ioc x (0 : ℝ),
        (∫⁻ t in Set.Iic (0 : ℝ), (Set.Ioc s (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t ∂σ) =
          ENNReal.ofReal (rderiv ϕ 0 - rderiv ϕ s) := by
      intro s hs
      rw [lintegral_indicator measurableSet_Ioc, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ioc]
      have : Set.Ioc s (0 : ℝ) ∩ Set.Iic (0 : ℝ) = Set.Ioc s (0 : ℝ) :=
        inter_eq_left.mpr Ioc_subset_Iic_self
      rw [this, StieltjesFunction.measure_Ioc]
      rfl
    rw [setLIntegral_congr_fun measurableSet_Ioc hslice]
    have hint : IntegrableOn (fun s => rderiv ϕ 0 - rderiv ϕ s) (Set.Ioc x (0 : ℝ)) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le]
      exact intervalIntegrable_const.sub (convexOn_monotone_rderiv hϕ).intervalIntegrable
    have hnn : ∀ s ∈ Set.Ioc x (0 : ℝ), 0 ≤ rderiv ϕ 0 - rderiv ϕ s := fun s hs =>
      sub_nonneg.mpr (convexOn_monotone_rderiv hϕ hs.2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hnn)),
        ← intervalIntegral.integral_of_le hx.le,
        intervalIntegral.integral_sub intervalIntegrable_const (convexOn_monotone_rderiv hϕ).intervalIntegrable,
        convexOn_ftc hϕ hx.le, intervalIntegral.integral_const, smul_eq_mul]
    congr 1; ring

/-! ### Module 3: Potential function properties -/

lemma potential_convexOn {α : Measure ℝ} (hα : MartOT.Var.InM α) :
    ConvexOn ℝ Set.univ (MartOT.Var.potential α) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, MartOT.Var.potential]
  calc ∫ y, |y - (a * x₁ + b * x₂)| ∂α
      ≤ ∫ y, (a * |y - x₁| + b * |y - x₂|) ∂α := by
        refine integral_mono (inM_integrable_abs_sub hα _)
          (((inM_integrable_abs_sub hα x₁).const_mul a).add ((inM_integrable_abs_sub hα x₂).const_mul b))
          (fun y => ?_)
        have hkey : y - (a * x₁ + b * x₂) = a * (y - x₁) + b * (y - x₂) := by
          calc y - (a * x₁ + b * x₂) = (a + b) * y - (a * x₁ + b * x₂) := by rw [hab, one_mul]
          _ = a * (y - x₁) + b * (y - x₂) := by ring
        rw [hkey]
        calc |a * (y - x₁) + b * (y - x₂)|
            ≤ |a * (y - x₁)| + |b * (y - x₂)| := abs_add_le _ _
          _ = a * |y - x₁| + b * |y - x₂| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ = a * ∫ y, |y - x₁| ∂α + b * ∫ y, |y - x₂| ∂α := by
        rw [integral_add ((inM_integrable_abs_sub hα x₁).const_mul a)
              ((inM_integrable_abs_sub hα x₂).const_mul b),
            integral_const_mul, integral_const_mul]

lemma potential_hasDerivWithinAt_Ioi {α : Measure ℝ} (hα : MartOT.Var.InM α) (a : ℝ) :
    HasDerivWithinAt (MartOT.Var.potential α)
      (2 * (α (Set.Iic a)).toReal - (α Set.univ).toReal) (Set.Ioi a) a := by
  have : IsFiniteMeasure α := hα.1
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  have hslope_eq : ∀ b ∈ Set.Ioi a,
      slope (MartOT.Var.potential α) a b = ∫ y, (|y - b| - |y - a|) / (b - a) ∂α := by
    intro b hb
    rw [slope_def_field, MartOT.Var.potential, MartOT.Var.potential,
        ← integral_sub (inM_integrable_abs_sub hα b) (inM_integrable_abs_sub hα a),
        ← integral_div]
  refine (Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (hslope_eq b hb).symm) ?_)
  have hlim_eq : 2 * (α (Set.Iic a)).toReal - (α Set.univ).toReal =
      ∫ y, (2 * (Set.Iic a).indicator (fun _ => (1 : ℝ)) y - 1) ∂α := by
    rw [integral_sub ((integrable_const (1 : ℝ)).indicator measurableSet_Iic |>.const_mul 2)
          (integrable_const (1 : ℝ)),
        integral_const_mul, integral_indicator_const _ measurableSet_Iic,
        integral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    rfl
  rw [hlim_eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall fun b => ?_)
    (by
      filter_upwards [self_mem_nhdsWithin] with b hb
      refine ae_of_all _ fun y => ?_
      have hba : 0 < b - a := sub_pos.mpr (mem_Ioi.mp hb)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hba, div_le_one hba]
      calc abs (|y - b| - |y - a|) ≤ |(y - b) - (y - a)| := abs_abs_sub_abs_le _ _
        _ = |a - b| := by ring_nf
        _ = b - a := by rw [abs_sub_comm, abs_of_pos hba])
    (integrable_const (1 : ℝ))
    (ae_of_all _ fun y => ?_)
  · exact (by fun_prop : Continuous fun y => (|y - b| - |y - a|) / (b - a)).aestronglyMeasurable
  · by_cases hy : y ≤ a
    · simp only [Set.indicator_of_mem (mem_Iic.mpr hy), mul_one]
      norm_num
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with b hb
      have hba : 0 < b - a := sub_pos.mpr (mem_Ioi.mp hb)
      rw [abs_of_nonpos (by linarith [mem_Ioi.mp hb] : y - b ≤ 0),
          abs_of_nonpos (by linarith : y - a ≤ 0)]
      field_simp [hba.ne']
      ring
    · push Not at hy
      have hnot : y ∉ Set.Iic a := not_le.mpr hy
      simp only [Set.indicator_of_notMem hnot, mul_zero, zero_sub]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hy] with b hb
      have hba : 0 < b - a := sub_pos.mpr hb.1
      rw [abs_of_pos (by linarith [hb.2] : 0 < y - b),
          abs_of_pos (by linarith : 0 < y - a)]
      field_simp [hba.ne']
      ring

lemma potential_hasDerivWithinAt_Iio {α : Measure ℝ} (hα : MartOT.Var.InM α) (a : ℝ) :
    HasDerivWithinAt (MartOT.Var.potential α)
      (2 * (α (Set.Iio a)).toReal - (α Set.univ).toReal) (Set.Iio a) a := by
  have : IsFiniteMeasure α := hα.1
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio]
  have hslope_eq : ∀ b ∈ Set.Iio a,
      slope (MartOT.Var.potential α) a b = ∫ y, (|y - b| - |y - a|) / (b - a) ∂α := by
    intro b hb
    rw [slope_def_field, MartOT.Var.potential, MartOT.Var.potential,
        ← integral_sub (inM_integrable_abs_sub hα b) (inM_integrable_abs_sub hα a),
        ← integral_div]
  refine (Tendsto.congr' (by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (hslope_eq b hb).symm) ?_)
  have hlim_eq : 2 * (α (Set.Iio a)).toReal - (α Set.univ).toReal =
      ∫ y, (2 * (Set.Iio a).indicator (fun _ => (1 : ℝ)) y - 1) ∂α := by
    rw [integral_sub ((integrable_const (1 : ℝ)).indicator measurableSet_Iio |>.const_mul 2)
          (integrable_const (1 : ℝ)),
        integral_const_mul, integral_indicator_const _ measurableSet_Iio,
        integral_const, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    rfl
  rw [hlim_eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall fun b => ?_)
    (by
      filter_upwards [self_mem_nhdsWithin] with b hb
      refine ae_of_all _ fun y => ?_
      have hab : 0 < a - b := sub_pos.mpr (mem_Iio.mp hb)
      rw [Real.norm_eq_abs, abs_div, abs_sub_comm b a, abs_of_pos hab, div_le_one hab]
      calc abs (|y - b| - |y - a|) ≤ |(y - b) - (y - a)| := abs_abs_sub_abs_le _ _
        _ = |a - b| := by ring_nf
        _ = a - b := abs_of_pos hab)
    (integrable_const (1 : ℝ))
    (ae_of_all _ fun y => ?_)
  · exact (by fun_prop : Continuous fun y => (|y - b| - |y - a|) / (b - a)).aestronglyMeasurable
  · by_cases hy : y < a
    · simp only [Set.indicator_of_mem (mem_Iio.mpr hy), mul_one]
      norm_num
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hy] with b hb
      have hba : b - a ≠ 0 := sub_ne_zero.mpr hb.2.ne
      rw [abs_of_neg (by linarith [hb.1] : y - b < 0),
          abs_of_neg (by linarith : y - a < 0)]
      field_simp [hba]
      ring
    · push Not at hy
      have hnot : y ∉ Set.Iio a := not_lt.mpr hy
      simp only [Set.indicator_of_notMem hnot, mul_zero, zero_sub]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with b hb
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (mem_Iio.mp hb).ne
      rw [abs_of_nonneg (by linarith [mem_Iio.mp hb] : 0 ≤ y - b),
          abs_of_nonneg (by linarith : 0 ≤ y - a)]
      field_simp [hba]
      ring

lemma potential_rderiv {α : Measure ℝ} (hα : MartOT.Var.InM α) (a : ℝ) :
    rderiv (MartOT.Var.potential α) a = 2 * (α (Set.Iic a)).toReal - (α Set.univ).toReal :=
  (potential_hasDerivWithinAt_Ioi hα a).derivWithin (uniqueDiffWithinAt_Ioi a)

lemma potential_lderiv {α : Measure ℝ} (hα : MartOT.Var.InM α) (a : ℝ) :
    lderiv (MartOT.Var.potential α) a = 2 * (α (Set.Iio a)).toReal - (α Set.univ).toReal :=
  (potential_hasDerivWithinAt_Iio hα a).derivWithin (uniqueDiffWithinAt_Iio a)

lemma integrable_max_sub_zero {α : Measure ℝ} (hα : MartOT.Var.InM α) (x : ℝ) :
    Integrable (fun y : ℝ => max (y - x) 0) α := by
  have : IsFiniteMeasure α := hα.1
  exact (hα.2.sub (integrable_const x)).pos_part

lemma integrable_max_zero_sub {α : Measure ℝ} (hα : MartOT.Var.InM α) (x : ℝ) :
    Integrable (fun y : ℝ => max (x - y) 0) α := by
  have : IsFiniteMeasure α := hα.1
  exact ((integrable_const x).sub hα.2).pos_part

lemma potential_sub_right_asymptote {α : Measure ℝ} (hα : MartOT.Var.InM α) (x : ℝ) :
    MartOT.Var.potential α x - ((α Set.univ).toReal * x - ∫ y, y ∂α) =
      2 * ∫ y, max (y - x) 0 ∂α := by
  have : IsFiniteMeasure α := hα.1
  have h1 : (α Set.univ).toReal * x - ∫ y, y ∂α = ∫ y, (x - y) ∂α := by
    rw [integral_sub (integrable_const x) hα.2, integral_const, smul_eq_mul]
    rfl
  have hsub : Integrable (fun y : ℝ => x - y) α := (integrable_const x).sub hα.2
  rw [h1, MartOT.Var.potential,
      ← integral_sub (inM_integrable_abs_sub hα x) hsub,
      ← integral_const_mul]
  congr 1; ext y
  rcases le_total y x with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring

lemma potential_sub_left_asymptote {α : Measure ℝ} (hα : MartOT.Var.InM α) (x : ℝ) :
    MartOT.Var.potential α x - ((∫ y, y ∂α) - (α Set.univ).toReal * x) =
      2 * ∫ y, max (x - y) 0 ∂α := by
  have : IsFiniteMeasure α := hα.1
  have h1 : (∫ y, y ∂α) - (α Set.univ).toReal * x = ∫ y, (y - x) ∂α := by
    rw [integral_sub hα.2 (integrable_const x), integral_const, smul_eq_mul]
    rfl
  have hsub : Integrable (fun y : ℝ => y - x) α := hα.2.sub (integrable_const x)
  rw [h1, MartOT.Var.potential,
      ← integral_sub (inM_integrable_abs_sub hα x) hsub,
      ← integral_const_mul]
  congr 1; ext y
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]; ring

lemma tendsto_integral_max_sub_atTop {α : Measure ℝ} (hα : MartOT.Var.InM α) :
    Tendsto (fun x : ℝ => ∫ y, max (y - x) 0 ∂α) atTop (𝓝 0) := by
  rw [show 𝓝 (0 : ℝ) = 𝓝 (∫ _ : ℝ, (0 : ℝ) ∂α) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|)
    (Eventually.of_forall fun x => (by fun_prop : Continuous fun y => max (y - x) 0).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_abs_self y]) (abs_nonneg y))
    (by simpa [Real.norm_eq_abs] using hα.2.norm)
    (ae_of_all _ fun y => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop y] with x hx
  simp [max_eq_right (sub_nonpos.mpr hx)]

lemma tendsto_integral_max_sub_atBot {α : Measure ℝ} (hα : MartOT.Var.InM α) :
    Tendsto (fun x : ℝ => ∫ y, max (x - y) 0 ∂α) atBot (𝓝 0) := by
  rw [show 𝓝 (0 : ℝ) = 𝓝 (∫ _ : ℝ, (0 : ℝ) ∂α) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => |y|)
    (Eventually.of_forall fun x => (by fun_prop : Continuous fun y => max (x - y) 0).aestronglyMeasurable)
    (by
      filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
      refine ae_of_all _ fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [neg_le_abs y]) (abs_nonneg y))
    (by simpa [Real.norm_eq_abs] using hα.2.norm)
    (ae_of_all _ fun y => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_le_atBot y] with x hx
  simp [max_eq_right (sub_nonpos.mpr hx)]

lemma potential_diff_convex_of_le {α β : Measure ℝ} (hβ : MartOT.Var.InM β) (hle : α ≤ β) :
    ConvexOn ℝ Set.univ (fun x => MartOT.Var.potential β x - MartOT.Var.potential α x) := by
  have : IsFiniteMeasure β := hβ.1
  have : IsFiniteMeasure α := isFiniteMeasure_of_le β hle
  have hα : MartOT.Var.InM α := ⟨inferInstance, hβ.2.mono_measure hle⟩
  set γ : Measure ℝ := β - α
  have hγ_le : γ ≤ β := Measure.sub_le
  have : IsFiniteMeasure γ := isFiniteMeasure_of_le β hγ_le
  have hγ : MartOT.Var.InM γ := ⟨inferInstance, hβ.2.mono_measure hγ_le⟩
  have hdecomp : γ + α = β := Measure.sub_add_cancel_of_le hle
  have heq : (fun x => MartOT.Var.potential β x - MartOT.Var.potential α x) =
      MartOT.Var.potential γ := by
    ext x
    unfold MartOT.Var.potential
    conv_lhs => rw [← hdecomp]
    rw [integral_add_measure (inM_integrable_abs_sub hγ x) (inM_integrable_abs_sub hα x)]
    ring
  rw [heq]
  exact potential_convexOn hγ

/-! ### Module 4: Reconstructing a measure in `InM` from a convex potential with asymptotes -/

lemma rderiv_tendsto_atTop {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {k m : ℝ}
    (htop : Tendsto (fun x => u x - (k * x - m)) atTop (𝓝 0)) :
    Tendsto (rderiv u) atTop (𝓝 k) := by
  have hle : ∀ x : ℝ, rderiv u x ≤ k := by
    intro x
    have hslope_lim : Tendsto (fun y => slope u x y) atTop (𝓝 k) := by
      have h1 : Tendsto (fun y : ℝ => k + ((u y - (k * y - m)) + (k * x - m - u x)) / (y - x))
          atTop (𝓝 (k + 0)) := by
        refine tendsto_const_nhds.add ?_
        have hnum : Tendsto (fun y : ℝ => (u y - (k * y - m)) + (k * x - m - u x))
            atTop (𝓝 (0 + (k * x - m - u x))) := htop.add tendsto_const_nhds
        have hden : Tendsto (fun y : ℝ => y - x) atTop atTop :=
          tendsto_id.atTop_add tendsto_const_nhds
        exact hnum.div_atTop hden
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop x] with y hy
      have hyx : y - x ≠ 0 := sub_ne_zero.mpr hy.ne'
      rw [slope_def_field]
      field_simp [hyx]
      ring
    refine ge_of_tendsto hslope_lim ?_
    filter_upwards [eventually_gt_atTop x] with y hy
    exact convexOn_rderiv_le_slope hu hy
  have hlow_lim : Tendsto (fun x : ℝ => slope u 0 x) atTop (𝓝 k) := by
    have h1 : Tendsto (fun x : ℝ => k + ((u x - (k * x - m)) + (-m - u 0)) / x)
        atTop (𝓝 (k + 0)) := by
      refine tendsto_const_nhds.add ?_
      exact (htop.add tendsto_const_nhds).div_atTop tendsto_id
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [slope_def_field, sub_zero]
    field_simp [hx.ne']
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim tendsto_const_nhds ?_
    (Eventually.of_forall hle)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact convexOn_slope_le_rderiv hu hx

lemma rderiv_tendsto_atBot {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {k m : ℝ}
    (hbot : Tendsto (fun x => u x - (m - k * x)) atBot (𝓝 0)) :
    Tendsto (rderiv u) atBot (𝓝 (-k)) := by
  have hge : ∀ x : ℝ, -k ≤ rderiv u x := by
    intro x
    have hslope_lim : Tendsto (fun z => slope u z x) atBot (𝓝 (-k)) := by
      have h1 : Tendsto (fun z : ℝ => -k + (u x - m + k * x - (u z - (m - k * z))) / (x - z))
          atBot (𝓝 (-k + 0)) := by
        refine tendsto_const_nhds.add ?_
        have hnum : Tendsto (fun z : ℝ => (u x - m + k * x) - (u z - (m - k * z)))
            atBot (𝓝 ((u x - m + k * x) - 0)) := tendsto_const_nhds.sub hbot
        have hden : Tendsto (fun z : ℝ => x - z) atBot atTop := by
          have : (fun z : ℝ => x - z) = (fun z => -z + x) := by ext z; ring
          rw [this]
          exact tendsto_neg_atBot_atTop.atTop_add tendsto_const_nhds
        exact hnum.div_atTop hden
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_lt_atBot x] with z hz
      have hxz : x - z ≠ 0 := sub_ne_zero.mpr hz.ne'
      rw [slope_def_field]
      field_simp [hxz]
      ring
    refine le_of_tendsto hslope_lim ?_
    filter_upwards [eventually_lt_atBot x] with z hz
    exact convexOn_slope_le_rderiv hu hz
  have hup_lim : Tendsto (fun x : ℝ => slope u x 0) atBot (𝓝 (-k)) := by
    have h1 : Tendsto (fun x : ℝ => -k + (u 0 - m - (u x - (m - k * x))) / (-x))
        atBot (𝓝 (-k + 0)) := by
      refine tendsto_const_nhds.add ?_
      exact (tendsto_const_nhds.sub hbot).div_atTop tendsto_neg_atBot_atTop
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    rw [slope_def_field, zero_sub]
    field_simp [hx.ne]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup_lim
    (Eventually.of_forall hge) ?_
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
  exact convexOn_rderiv_le_slope hu hx

noncomputable def potentialStieltjes (u : ℝ → ℝ) (hu : ConvexOn ℝ Set.univ u) (k : ℝ) :
    StieltjesFunction ℝ where
  toFun x := (rderiv u x + k) / 2
  mono' := fun _ _ hxy => by linarith [convexOn_monotone_rderiv hu hxy]
  right_continuous' := fun x =>
    ((convexOn_rderiv_continuousWithinAt hu x).add continuousWithinAt_const).div_const 2

lemma measure_of_convex_props {u : ℝ → ℝ} (hu : ConvexOn ℝ Set.univ u) {k m : ℝ} (hk : 0 ≤ k)
    (htop : Tendsto (fun x => u x - (k * x - m)) atTop (𝓝 0))
    (hbot : Tendsto (fun x => u x - (m - k * x)) atBot (𝓝 0)) :
    let F := potentialStieltjes u hu k
    let α := F.measure
    MartOT.Var.InM α ∧
      α Set.univ = ENNReal.ofReal k ∧
      (∫ y, y ∂α) = m ∧
      ∀ a : ℝ, MartOT.Var.potential α a = u a := by
  intro F α
  have hF_top : Tendsto F atTop (𝓝 k) := by
    have h1 : Tendsto (fun x => (rderiv u x + k) / 2) atTop (𝓝 ((k + k) / 2)) :=
      ((rderiv_tendsto_atTop hu htop).add tendsto_const_nhds).div_const 2
    simpa [F, potentialStieltjes, add_halves] using h1
  have hF_bot : Tendsto F atBot (𝓝 0) := by
    have h1 : Tendsto (fun x => (rderiv u x + k) / 2) atBot (𝓝 ((-k + k) / 2)) :=
      ((rderiv_tendsto_atBot hu hbot).add tendsto_const_nhds).div_const 2
    simpa [F, potentialStieltjes] using h1
  have hfin : IsFiniteMeasure α := F.isFiniteMeasure hF_bot hF_top
  have huniv : α Set.univ = ENNReal.ofReal k := by
    simpa using F.measure_univ hF_bot hF_top
  have hF_le : ∀ x, F x ≤ k := fun x =>
    ge_of_tendsto hF_top ((eventually_ge_atTop x).mono fun _ hy => F.mono hy)
  have hF_nn : ∀ x, 0 ≤ F x := fun x =>
    le_of_tendsto hF_bot ((eventually_le_atBot x).mono fun _ hy => F.mono hy)
  -- Compute lintegral of max (y - a) 0 via Tonelli + monotone convergence + FTC
  have hlint_pos : ∀ a : ℝ,
      ∫⁻ y, ENNReal.ofReal (max (y - a) 0) ∂α = ENNReal.ofReal ((u a - (k * a - m)) / 2) := by
    intro a
    have hinner : ∀ y : ℝ, ENNReal.ofReal (max (y - a) 0) =
        ∫⁻ t in Set.Ioi a, (Set.Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) y ∂volume := by
      intro y
      have hset : ∀ t ∈ Set.Ioi a,
          (Set.Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) y =
            (Set.Iio y).indicator (fun _ => (1 : ℝ≥0∞)) t := by
        intro t _
        by_cases h : t < y <;> simp [Set.indicator, mem_Ioi, mem_Iio, h]
      rw [setLIntegral_congr_fun measurableSet_Ioi hset,
          lintegral_indicator measurableSet_Iio, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iio]
      by_cases hay : a < y
      · have : Set.Iio y ∩ Set.Ioi a = Set.Ioo a y := by
          ext t; simp [mem_Iio, mem_Ioi, mem_Ioo, and_comm]
        rw [this, Real.volume_Ioo, max_eq_left (sub_nonneg.mpr hay.le)]
      · have : Set.Iio y ∩ Set.Ioi a = ∅ := by
          ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; linarith
        rw [this, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
    simp_rw [hinner]
    have hmeas : Measurable (Function.uncurry fun y t : ℝ =>
        (Set.Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
      have hS : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
        measurableSet_lt measurable_snd measurable_fst
      have heq : (Function.uncurry fun y t : ℝ =>
          (Set.Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) y) =
          Set.indicator {p : ℝ × ℝ | p.2 < p.1} (fun _ => (1 : ℝ≥0∞)) := by
        ext ⟨y, t⟩; by_cases h : t < y <;> simp [Function.uncurry, Set.indicator, mem_Ioi, h]
      rw [heq]; exact measurable_const.indicator hS
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hslice : ∀ t ∈ Set.Ioi a,
        (∫⁻ y, (Set.Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) y ∂α) = ENNReal.ofReal (k - F t) := by
      intro t _
      rw [lintegral_indicator measurableSet_Ioi, lintegral_const, one_mul,
          Measure.restrict_apply_univ, F.measure_Ioi hF_top t]
    rw [setLIntegral_congr_fun measurableSet_Ioi hslice]
    -- Evaluate ∫⁻ t in Ioi a, ofReal (k - F t) via iSup over Ioc a (a + n)
    let g : ℕ → ℝ → ℝ≥0∞ := fun n t => (Set.Ioc a (a + (n : ℝ))).indicator (fun t => ENNReal.ofReal (k - F t)) t
    have hg_meas : ∀ n, Measurable (g n) := fun n =>
      (ENNReal.measurable_ofReal.comp (measurable_const.sub F.mono.measurable)).indicator measurableSet_Ioc
    have hg_mono : Monotone g := by
      intro n₁ n₂ hle t
      by_cases ht : t ∈ Set.Ioc a (a + (n₁ : ℝ))
      · have ht2 : t ∈ Set.Ioc a (a + (n₂ : ℝ)) :=
          ⟨ht.1, by linarith [ht.2, Nat.cast_le (α := ℝ).mpr hle]⟩
        simp [g, Set.indicator_of_mem ht, Set.indicator_of_mem ht2]
      · simp [g, Set.indicator_of_notMem ht]
    have hg_iSup : ∀ t, (⨆ n, g n t) = (Set.Ioi a).indicator (fun t => ENNReal.ofReal (k - F t)) t := by
      intro t
      by_cases ht : a < t
      · simp only [Set.indicator_of_mem (mem_Ioi.mpr ht)]
        refine le_antisymm (iSup_le fun n => ?_) ?_
        · by_cases h : t ∈ Set.Ioc a (a + (n : ℝ))
          · rw [show g n t = ENNReal.ofReal (k - F t) from Set.indicator_of_mem h _]
          · rw [show g n t = 0 from Set.indicator_of_notMem h _]; exact zero_le
        · obtain ⟨n, hn⟩ := exists_nat_gt (t - a)
          refine le_iSup_of_le n ?_
          have hmem : t ∈ Set.Ioc a (a + (n : ℝ)) := ⟨ht, by linarith⟩
          simp [g, Set.indicator_of_mem hmem]
      · have hnot_ioi : t ∉ Set.Ioi a := ht
        simp only [Set.indicator_of_notMem hnot_ioi]
        refine le_antisymm (iSup_le fun n => ?_) (zero_le)
        have hnot : t ∉ Set.Ioc a (a + (n : ℝ)) := fun h => ht h.1
        simp [g, Set.indicator_of_notMem hnot]
    have hstep : ∀ n : ℕ, ∫⁻ t, g n t ∂volume =
        ENNReal.ofReal (((u a - (k * a - m)) - (u (a + n) - (k * (a + n) - m))) / 2) := by
      intro n
      dsimp only [g]
      rw [lintegral_indicator measurableSet_Ioc]
      have hab : a ≤ a + (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hint : IntegrableOn (fun t => k - F t) (Set.Ioc a (a + (n : ℝ))) volume := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
        exact intervalIntegrable_const.sub F.mono.intervalIntegrable
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun t => sub_nonneg.mpr (hF_le t)),
          ← intervalIntegral.integral_of_le hab]
      congr 1
      have hF_eq : (fun t => k - F t) = (fun t => (k - rderiv u t) / 2) := by
        ext t; change k - (rderiv u t + k) / 2 = _; ring
      rw [hF_eq, intervalIntegral.integral_div,
          intervalIntegral.integral_sub intervalIntegrable_const (convexOn_monotone_rderiv hu).intervalIntegrable,
          intervalIntegral.integral_const, convexOn_ftc hu hab, smul_eq_mul]
      ring
    have hLHS : ∫⁻ t in Set.Ioi a, ENNReal.ofReal (k - F t) ∂volume = ⨆ n, ∫⁻ t, g n t ∂volume := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_iSup hg_meas hg_mono]
      congr 1; ext t; exact (hg_iSup t).symm
    rw [hLHS]
    have htend1 : Tendsto (fun n => ∫⁻ t, g n t ∂volume) atTop (𝓝 (⨆ n, ∫⁻ t, g n t ∂volume)) :=
      tendsto_atTop_iSup fun _ _ hle => lintegral_mono (hg_mono hle)
    have htend2 : Tendsto (fun n : ℕ => ∫⁻ t, g n t ∂volume) atTop
        (𝓝 (ENNReal.ofReal ((u a - (k * a - m)) / 2))) := by
      simp_rw [hstep]
      refine ENNReal.tendsto_ofReal ?_
      have hshift : Tendsto (fun n : ℕ => u (a + (n : ℝ)) - (k * (a + (n : ℝ)) - m)) atTop (𝓝 0) :=
        htop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop)
      have h2 := ((tendsto_const_nhds (x := u a - (k * a - m))).sub hshift).div_const (2 : ℝ)
      simpa using h2
    exact tendsto_nhds_unique htend1 htend2
  -- Compute lintegral of max (a - y) 0 via Tonelli + monotone convergence + FTC
  have hlint_neg : ∀ a : ℝ,
      ∫⁻ y, ENNReal.ofReal (max (a - y) 0) ∂α = ENNReal.ofReal ((u a - (m - k * a)) / 2) := by
    intro a
    have hinner : ∀ y : ℝ, ENNReal.ofReal (max (a - y) 0) =
        ∫⁻ t in Set.Iio a, (Set.Iic t).indicator (fun _ => (1 : ℝ≥0∞)) y ∂volume := by
      intro y
      have hset : ∀ t ∈ Set.Iio a,
          (Set.Iic t).indicator (fun _ => (1 : ℝ≥0∞)) y =
            (Set.Ici y).indicator (fun _ => (1 : ℝ≥0∞)) t := by
        intro t _
        by_cases h : y ≤ t <;> simp [Set.indicator, mem_Iic, mem_Ici, h]
      rw [setLIntegral_congr_fun measurableSet_Iio hset,
          lintegral_indicator measurableSet_Ici, lintegral_const, one_mul,
          Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ici]
      by_cases hya : y < a
      · have : Set.Ici y ∩ Set.Iio a = Set.Ico y a := by
          ext t; simp [mem_Ici, mem_Iio, mem_Ico]
        rw [this, Real.volume_Ico, max_eq_left (sub_nonneg.mpr hya.le)]
      · have : Set.Ici y ∩ Set.Iio a = ∅ := by
          ext t; simp only [mem_inter_iff, mem_Ici, mem_Iio, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2; linarith
        rw [this, measure_empty, max_eq_right (by linarith), ENNReal.ofReal_zero]
    simp_rw [hinner]
    have hmeas : Measurable (Function.uncurry fun y t : ℝ =>
        (Set.Iic t).indicator (fun _ => (1 : ℝ≥0∞)) y) := by
      have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
        measurableSet_le measurable_fst measurable_snd
      have heq : (Function.uncurry fun y t : ℝ =>
          (Set.Iic t).indicator (fun _ => (1 : ℝ≥0∞)) y) =
          Set.indicator {p : ℝ × ℝ | p.1 ≤ p.2} (fun _ => (1 : ℝ≥0∞)) := by
        ext ⟨y, t⟩; by_cases h : y ≤ t <;> simp [Function.uncurry, Set.indicator, mem_Iic, h]
      rw [heq]; exact measurable_const.indicator hS
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hslice : ∀ t ∈ Set.Iio a,
        (∫⁻ y, (Set.Iic t).indicator (fun _ => (1 : ℝ≥0∞)) y ∂α) = ENNReal.ofReal (F t) := by
      intro t _
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, one_mul,
          Measure.restrict_apply_univ, F.measure_Iic hF_bot t, sub_zero]
    rw [setLIntegral_congr_fun measurableSet_Iio hslice, setLIntegral_congr Iio_ae_eq_Iic]
    let g : ℕ → ℝ → ℝ≥0∞ := fun n t => (Set.Ioc (a - ((n : ℝ) + 1)) a).indicator (fun t => ENNReal.ofReal (F t)) t
    have hg_meas : ∀ n, Measurable (g n) := fun n =>
      (ENNReal.measurable_ofReal.comp F.mono.measurable).indicator measurableSet_Ioc
    have hg_mono : Monotone g := by
      intro n₁ n₂ hle t
      by_cases ht : t ∈ Set.Ioc (a - ((n₁ : ℝ) + 1)) a
      · have ht2 : t ∈ Set.Ioc (a - ((n₂ : ℝ) + 1)) a :=
          ⟨lt_of_le_of_lt (by linarith [Nat.cast_le (α := ℝ).mpr hle]) ht.1, ht.2⟩
        simp [g, Set.indicator_of_mem ht, Set.indicator_of_mem ht2]
      · simp [g, Set.indicator_of_notMem ht]
    have hg_iSup : ∀ t, (⨆ n, g n t) = (Set.Iic a).indicator (fun t => ENNReal.ofReal (F t)) t := by
      intro t
      by_cases ht : t ≤ a
      · simp only [Set.indicator_of_mem (mem_Iic.mpr ht)]
        refine le_antisymm (iSup_le fun n => ?_) ?_
        · by_cases h : t ∈ Set.Ioc (a - ((n : ℝ) + 1)) a
          · rw [show g n t = ENNReal.ofReal (F t) from Set.indicator_of_mem h _]
          · rw [show g n t = 0 from Set.indicator_of_notMem h _]; exact zero_le
        · obtain ⟨n, hn⟩ := exists_nat_gt (a - t)
          refine le_iSup_of_le n ?_
          have hmem : t ∈ Set.Ioc (a - ((n : ℝ) + 1)) a := ⟨by linarith, ht⟩
          simp [g, Set.indicator_of_mem hmem]
      · have hnot_iic : t ∉ Set.Iic a := ht
        simp only [Set.indicator_of_notMem hnot_iic]
        refine le_antisymm (iSup_le fun n => ?_) (zero_le)
        have hnot : t ∉ Set.Ioc (a - ((n : ℝ) + 1)) a := fun h => ht h.2
        simp [g, Set.indicator_of_notMem hnot]
    have hstep : ∀ n : ℕ, ∫⁻ t, g n t ∂volume =
        ENNReal.ofReal (((u a - (m - k * a)) - (u (a - ((n : ℝ) + 1)) - (m - k * (a - ((n : ℝ) + 1))))) / 2) := by
      intro n
      dsimp only [g]
      rw [lintegral_indicator measurableSet_Ioc]
      have hab : a - ((n : ℝ) + 1) ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hint : IntegrableOn (fun t => F t) (Set.Ioc (a - ((n : ℝ) + 1)) a) volume := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
        exact F.mono.intervalIntegrable
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF_nn),
          ← intervalIntegral.integral_of_le hab]
      congr 1
      have hF_eq : (fun t => F t) = (fun t => (rderiv u t + k) / 2) := rfl
      rw [hF_eq, intervalIntegral.integral_div,
          intervalIntegral.integral_add (convexOn_monotone_rderiv hu).intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const, convexOn_ftc hu hab, smul_eq_mul]
      ring
    have hLHS : ∫⁻ t in Set.Iic a, ENNReal.ofReal (F t) ∂volume = ⨆ n, ∫⁻ t, g n t ∂volume := by
      rw [← lintegral_indicator measurableSet_Iic, ← lintegral_iSup hg_meas hg_mono]
      congr 1; ext t; exact (hg_iSup t).symm
    rw [hLHS]
    have htend1 : Tendsto (fun n => ∫⁻ t, g n t ∂volume) atTop (𝓝 (⨆ n, ∫⁻ t, g n t ∂volume)) :=
      tendsto_atTop_iSup fun _ _ hle => lintegral_mono (hg_mono hle)
    have htend2 : Tendsto (fun n : ℕ => ∫⁻ t, g n t ∂volume) atTop
        (𝓝 (ENNReal.ofReal ((u a - (m - k * a)) / 2))) := by
      simp_rw [hstep]
      refine ENNReal.tendsto_ofReal ?_
      have harg : Tendsto (fun n : ℕ => a - ((n : ℝ) + 1)) atTop atBot := by
        have : (fun n : ℕ => a - ((n : ℝ) + 1)) = (fun n : ℕ => -((n : ℝ) + 1) + a) := by ext n; ring
        rw [this]
        exact (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).atBot_add
          tendsto_const_nhds
      have hshift : Tendsto (fun n : ℕ => u (a - ((n : ℝ) + 1)) - (m - k * (a - ((n : ℝ) + 1)))) atTop (𝓝 0) :=
        hbot.comp harg
      have h2 := ((tendsto_const_nhds (x := u a - (m - k * a))).sub hshift).div_const (2 : ℝ)
      simpa using h2
    exact tendsto_nhds_unique htend1 htend2
  -- First moment finiteness (InM α)
  have hInM : MartOT.Var.InM α := by
    refine ⟨hfin, ⟨aestronglyMeasurable_id, ?_⟩⟩
    rw [HasFiniteIntegral]
    have hnorm : ∀ y : ℝ, ‖y‖ₑ = ENNReal.ofReal (max (y - 0) 0) + ENNReal.ofReal (max (0 - y) 0) := by
      intro y
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
      congr 1
      rcases le_total y 0 with h | h
      · rw [abs_of_nonpos h, sub_zero, zero_sub, max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [abs_of_nonneg h, sub_zero, zero_sub, max_eq_left h, max_eq_right (by linarith)]; ring
    simp_rw [hnorm]
    rw [lintegral_add_left (by fun_prop), hlint_pos 0, hlint_neg 0]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  -- Sign of (u a - (k * a - m)) and (u a - (m - k * a))
  have hpos_nn : ∀ a : ℝ, 0 ≤ (u a - (k * a - m)) / 2 := by
    intro a
    have h1 : ∀ n : ℕ, (u a - (k * a - m)) - (u (a + (n : ℝ)) - (k * (a + (n : ℝ)) - m)) ≥ 0 := by
      intro n
      have hab : a ≤ a + (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 := convexOn_ftc hu hab
      have h3 : ∫ t in a..(a + (n : ℝ)), rderiv u t ≤ ∫ _ in a..(a + (n : ℝ)), k := by
        refine intervalIntegral.integral_mono_on hab (convexOn_monotone_rderiv hu).intervalIntegrable
          intervalIntegrable_const fun t _ => ?_
        have hle_t : (rderiv u t + k) / 2 ≤ k := hF_le t
        linarith
      rw [h2, intervalIntegral.integral_const, smul_eq_mul] at h3
      linarith
    have hlim : Tendsto (fun n : ℕ => (u a - (k * a - m)) - (u (a + (n : ℝ)) - (k * (a + (n : ℝ)) - m)))
        atTop (𝓝 (u a - (k * a - m))) := by
      simpa using (tendsto_const_nhds (x := u a - (k * a - m))).sub
        (htop.comp (tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop))
    have : 0 ≤ u a - (k * a - m) := ge_of_tendsto hlim (Eventually.of_forall h1)
    linarith
  have hneg_nn : ∀ a : ℝ, 0 ≤ (u a - (m - k * a)) / 2 := by
    intro a
    have h1 : ∀ n : ℕ, (u a - (m - k * a)) - (u (a - ((n : ℝ) + 1)) - (m - k * (a - ((n : ℝ) + 1)))) ≥ 0 := by
      intro n
      have hab : a - ((n : ℝ) + 1) ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 := convexOn_ftc hu hab
      have h3 : ∫ _ in (a - ((n : ℝ) + 1))..a, (-k) ≤ ∫ t in (a - ((n : ℝ) + 1))..a, rderiv u t := by
        refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (convexOn_monotone_rderiv hu).intervalIntegrable fun t _ => ?_
        have hnn_t : 0 ≤ (rderiv u t + k) / 2 := hF_nn t
        linarith
      rw [h2, intervalIntegral.integral_const, smul_eq_mul] at h3
      linarith
    have harg : Tendsto (fun n : ℕ => a - ((n : ℝ) + 1)) atTop atBot := by
      have : (fun n : ℕ => a - ((n : ℝ) + 1)) = (fun n : ℕ => -((n : ℝ) + 1) + a) := by ext n; ring
      rw [this]
      exact (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).atBot_add
        tendsto_const_nhds
    have hlim : Tendsto (fun n : ℕ => (u a - (m - k * a)) - (u (a - ((n : ℝ) + 1)) - (m - k * (a - ((n : ℝ) + 1)))))
        atTop (𝓝 (u a - (m - k * a))) := by
      simpa using (tendsto_const_nhds (x := u a - (m - k * a))).sub (hbot.comp harg)
    have : 0 ≤ u a - (m - k * a) := ge_of_tendsto hlim (Eventually.of_forall h1)
    linarith
  have hint_pos_eq : ∀ a : ℝ, ∫ y, max (y - a) 0 ∂α = (u a - (k * a - m)) / 2 := by
    intro a
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_max_sub_zero hInM a)
      (ae_of_all _ fun _ => le_max_right _ _)
    rw [hlint_pos a] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _) (hpos_nn a)).mp h1
  have hint_neg_eq : ∀ a : ℝ, ∫ y, max (a - y) 0 ∂α = (u a - (m - k * a)) / 2 := by
    intro a
    have h1 := ofReal_integral_eq_lintegral_ofReal (integrable_max_zero_sub hInM a)
      (ae_of_all _ fun _ => le_max_right _ _)
    rw [hlint_neg a] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => le_max_right _ _) (hneg_nn a)).mp h1
  have hmean : ∫ y, y ∂α = m := by
    have heq : (fun y : ℝ => y) = (fun y => max (y - 0) 0 - max (0 - y) 0) := by
      ext y; rcases le_total y 0 with h | h <;> simp [h]
    rw [heq, integral_sub (integrable_max_sub_zero hInM 0) (integrable_max_zero_sub hInM 0),
        hint_pos_eq 0, hint_neg_eq 0]
    ring
  have hpot : ∀ a : ℝ, MartOT.Var.potential α a = u a := by
    intro a
    unfold MartOT.Var.potential
    have heq : (fun y : ℝ => |y - a|) = (fun y => max (y - a) 0 + max (a - y) 0) := by
      ext y
      rcases le_total y a with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_right (sub_nonpos.mpr h),
            max_eq_left (sub_nonneg.mpr h)]; ring
      · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h),
            max_eq_right (sub_nonpos.mpr h)]; ring
    rw [heq, integral_add (integrable_max_sub_zero hInM a) (integrable_max_zero_sub hInM a),
        hint_pos_eq a, hint_neg_eq a]
    ring
  exact ⟨hInM, huniv, hmean, hpot⟩

/-! ### Module 5: `ConvexLE` from potential inequality -/

lemma convexLE_of_potential_le {α β : Measure ℝ}
    (hα : MartOT.Var.InM α) (hβ : MartOT.Var.InM β)
    (hmass : α Set.univ = β Set.univ)
    (hmean : ∫ y, y ∂α = ∫ y, y ∂β)
    (hpot : ∀ x : ℝ, MartOT.Var.potential α x ≤ MartOT.Var.potential β x) :
    MartOT.Var.ConvexLE α β := by
  have : IsFiniteMeasure α := hα.1
  have : IsFiniteMeasure β := hβ.1
  refine ⟨hα, hβ, fun ϕ hϕ => ?_⟩
  let a : ℝ → ℝ := fun x => ϕ 0 + rderiv ϕ 0 * x
  let ψ : ℝ → ℝ := fun x => ϕ x - a x
  have hϕ_eq : ϕ = fun x => ψ x + a x := by ext x; dsimp only [ψ]; ring
  have ha_α : Integrable a α := (integrable_const _).add (hα.2.const_mul _)
  have ha_β : Integrable a β := (integrable_const _).add (hβ.2.const_mul _)
  have ha_eq : ∫ x, a x ∂α = ∫ x, a x ∂β := by
    simp only [a]
    rw [integral_add (integrable_const _) (hα.2.const_mul _),
        integral_add (integrable_const _) (hβ.2.const_mul _),
        integral_const, integral_const, integral_const_mul, integral_const_mul,
        smul_eq_mul, smul_eq_mul, Measure.real, Measure.real, hmass, hmean]
  have hψ_meas : Measurable ψ := ((convexOn_continuous hϕ).sub (by fun_prop)).measurable
  have hψ_nn : ∀ x, 0 ≤ ψ x := convexOn_sub_support_nonneg hϕ
  rw [hϕ_eq, integralE_add_integrable hψ_meas hψ_nn ha_α,
      integralE_add_integrable hψ_meas hψ_nn ha_β, ha_eq]
  refine add_le_add ?_ le_rfl
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  set σ : Measure ℝ := (rderivStieltjes ϕ hϕ).measure
  have hrepr : ∀ x : ℝ, ENNReal.ofReal (ψ x) =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (x - t) 0) ∂σ) +
      (∫⁻ t in Set.Iic (0 : ℝ), ENNReal.ofReal (max (t - x) 0) ∂σ) :=
    fun x => convexOn_stieltjes_repr hϕ x
  have hswap : ∀ (γ : Measure ℝ), MartOT.Var.InM γ →
      ∫⁻ x, ENNReal.ofReal (ψ x) ∂γ =
        (∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (max (x - t) 0) ∂γ ∂σ) +
        (∫⁻ t in Set.Iic (0 : ℝ), ∫⁻ x, ENNReal.ofReal (max (t - x) 0) ∂γ ∂σ) := by
    intro γ hγ
    have : IsFiniteMeasure γ := hγ.1
    simp_rw [hrepr]
    have hm1 : Measurable (Function.uncurry fun x t : ℝ => ENNReal.ofReal (max (x - t) 0)) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).max measurable_const)
    have hm2 : Measurable (Function.uncurry fun x t : ℝ => ENNReal.ofReal (max (t - x) 0)) :=
      ENNReal.measurable_ofReal.comp ((measurable_snd.sub measurable_fst).max measurable_const)
    have hm1_l : Measurable (fun x => ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (max (x - t) 0) ∂σ) :=
      Measurable.lintegral_prod_right' hm1
    rw [lintegral_add_left hm1_l]
    congr 1
    · exact lintegral_lintegral_swap hm1.aemeasurable
    · exact lintegral_lintegral_swap hm2.aemeasurable
  rw [hswap α hα, hswap β hβ]
  refine add_le_add (lintegral_mono fun t => ?_) (lintegral_mono fun t => ?_)
  · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_max_sub_zero hα t) (ae_of_all _ fun _ => le_max_right _ _),
        ← ofReal_integral_eq_lintegral_ofReal (integrable_max_sub_zero hβ t) (ae_of_all _ fun _ => le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := potential_sub_right_asymptote hα t
    have h2 := potential_sub_right_asymptote hβ t
    have hp := hpot t
    rw [hmass, hmean] at h1
    linarith
  · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_max_zero_sub hα t) (ae_of_all _ fun _ => le_max_right _ _),
        ← ofReal_integral_eq_lintegral_ofReal (integrable_max_zero_sub hβ t) (ae_of_all _ fun _ => le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := potential_sub_left_asymptote hα t
    have h2 := potential_sub_left_asymptote hβ t
    have hp := hpot t
    rw [hmass, hmean] at h1
    linarith

/-! ### Module 6: `ConvergesInM` from pointwise convergence of potentials -/

lemma cdf_tendsto_of_potential_tendsto {αs : ℕ → Measure ℝ} {α : Measure ℝ}
    (hαs : ∀ n, MartOT.Var.InM (αs n)) (hα : MartOT.Var.InM α)
    (hmass : ∀ n, αs n Set.univ = α Set.univ)
    (hpot : ∀ x : ℝ, Tendsto (fun n => MartOT.Var.potential (αs n) x) atTop (𝓝 (MartOT.Var.potential α x)))
    {x : ℝ} (hx : α {x} = 0) :
    Tendsto (fun n => (αs n (Set.Iic x)).toReal) atTop (𝓝 ((α (Set.Iic x)).toReal)) := by
  have : IsFiniteMeasure α := hα.1
  have hu_conv : ConvexOn ℝ Set.univ (MartOT.Var.potential α) := potential_convexOn hα
  have hr_eq_l : lderiv (MartOT.Var.potential α) x = rderiv (MartOT.Var.potential α) x := by
    rw [potential_lderiv hα x, potential_rderiv hα x]
    have : α (Set.Iic x) = α (Set.Iio x) := by
      rw [← Set.Iio_union_right,
          measure_union (Set.disjoint_singleton_right.mpr Set.self_notMem_Iio) (measurableSet_singleton x),
          hx, add_zero]
    rw [this]
  -- Show rderiv (potential (αs n)) x → rderiv (potential α) x
  have hr_tend : Tendsto (fun n => rderiv (MartOT.Var.potential (αs n)) x) atTop
      (𝓝 (rderiv (MartOT.Var.potential α) x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hright_lim : Tendsto (slope (MartOT.Var.potential α) x) (𝓝[>] x)
        (𝓝 (rderiv (MartOT.Var.potential α) x)) :=
      (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp (convexOn_hasDerivWithinAt_rderiv hu_conv x)
    have hleft_lim : Tendsto (slope (MartOT.Var.potential α) x) (𝓝[<] x)
        (𝓝 (rderiv (MartOT.Var.potential α) x)) := by
      rw [← hr_eq_l]
      exact (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp (convexOn_hasDerivWithinAt_lderiv hu_conv x)
    obtain ⟨y₁, hy₁_gt, hy₁_lt⟩ : ∃ y₁, x < y₁ ∧
        slope (MartOT.Var.potential α) x y₁ < rderiv (MartOT.Var.potential α) x + ε / 2 := by
      have hmem : {y | slope (MartOT.Var.potential α) x y < rderiv (MartOT.Var.potential α) x + ε / 2} ∈ 𝓝[>] x :=
        hright_lim (Iio_mem_nhds (by linarith))
      obtain ⟨y₁, hy₁_lt, hy₁_gt⟩ := Filter.nonempty_of_mem (Filter.inter_mem hmem self_mem_nhdsWithin)
      exact ⟨y₁, hy₁_gt, hy₁_lt⟩
    obtain ⟨y₂, hy₂_lt, hy₂_gt⟩ : ∃ y₂, y₂ < x ∧
        rderiv (MartOT.Var.potential α) x - ε / 2 < slope (MartOT.Var.potential α) y₂ x := by
      have hmem : {y | rderiv (MartOT.Var.potential α) x - ε / 2 < slope (MartOT.Var.potential α) x y} ∈ 𝓝[<] x :=
        hleft_lim (Ioi_mem_nhds (by linarith))
      obtain ⟨y₂, hy₂_gt, hy₂_lt⟩ := Filter.nonempty_of_mem (Filter.inter_mem hmem self_mem_nhdsWithin)
      change rderiv (MartOT.Var.potential α) x - ε / 2 < slope (MartOT.Var.potential α) x y₂ at hy₂_gt
      exact ⟨y₂, hy₂_lt, by rwa [slope_comm] at hy₂_gt⟩
    have hsl1 : Tendsto (fun n => slope (MartOT.Var.potential (αs n)) x y₁) atTop
        (𝓝 (slope (MartOT.Var.potential α) x y₁)) := by
      simp only [slope_def_field]
      exact ((hpot y₁).sub (hpot x)).div_const (y₁ - x)
    have hsl2 : Tendsto (fun n => slope (MartOT.Var.potential (αs n)) y₂ x) atTop
        (𝓝 (slope (MartOT.Var.potential α) y₂ x)) := by
      simp only [slope_def_field]
      exact ((hpot x).sub (hpot y₂)).div_const (x - y₂)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hsl1 (Iio_mem_nhds (by linarith : slope (MartOT.Var.potential α) x y₁ < rderiv (MartOT.Var.potential α) x + ε)))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hsl2 (Ioi_mem_nhds (by linarith : rderiv (MartOT.Var.potential α) x - ε < slope (MartOT.Var.potential α) y₂ x)))
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hcv := potential_convexOn (hαs n)
    have hup : rderiv (MartOT.Var.potential (αs n)) x < rderiv (MartOT.Var.potential α) x + ε :=
      (convexOn_rderiv_le_slope hcv hy₁_gt).trans_lt (hN₁ n (le_trans (le_max_left _ _) hn))
    have hlo : rderiv (MartOT.Var.potential α) x - ε < rderiv (MartOT.Var.potential (αs n)) x :=
      (hN₂ n (le_trans (le_max_right _ _) hn)).trans_le (convexOn_slope_le_rderiv hcv hy₂_lt)
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  -- Recover (αs n (Iic x)).toReal = (rderiv + k) / 2
  have heq_n : ∀ n, (αs n (Set.Iic x)).toReal =
      (rderiv (MartOT.Var.potential (αs n)) x + (α Set.univ).toReal) / 2 := by
    intro n
    rw [potential_rderiv (hαs n) x, hmass n]
    ring
  have heq : (α (Set.Iic x)).toReal =
      (rderiv (MartOT.Var.potential α) x + (α Set.univ).toReal) / 2 := by
    rw [potential_rderiv hα x]
    ring
  simp_rw [heq_n, heq]
  exact (hr_tend.add tendsto_const_nhds).div_const 2

lemma countable_atoms (α : Measure ℝ) [IsFiniteMeasure α] :
    {x : ℝ | α {x} ≠ 0}.Countable := by
  have hsub : {x : ℝ | α {x} ≠ 0} ⊆ ⋃ m : ℕ, {x : ℝ | (1 : ℝ≥0∞) / (m + 1 : ℕ) ≤ α {x}} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    have hpos : 0 < α {x} := pos_iff_ne_zero.mpr hx
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 : ℝ≥0∞) / (m + 1 : ℕ) ≤ α {x} := by
      have htop_or : α {x} = ⊤ ∨ α {x} ≠ ⊤ := eq_or_ne _ _
      rcases htop_or with h | h
      · exact ⟨0, by simp [h]⟩
      · have htr : 0 < (α {x}).toReal := ENNReal.toReal_pos hx h
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt htr
        refine ⟨m, ?_⟩
        rw [← ENNReal.ofReal_toReal h]
        have hcast : (1 : ℝ≥0∞) / ((m + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
              ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,
              ENNReal.ofReal_natCast, ENNReal.ofReal_one, Nat.cast_add, Nat.cast_one]
        rw [hcast]
        exact ENNReal.ofReal_le_ofReal hm.le
    exact mem_iUnion.mpr ⟨m, hm⟩
  refine (Set.countable_iUnion fun m => ?_).mono hsub
  refine Set.Finite.countable ?_
  by_contra hinf
  have : Infinite {x : ℝ | (1 : ℝ≥0∞) / (m + 1 : ℕ) ≤ α {x}} := Set.infinite_coe_iff.mpr hinf
  -- Pick a finset of size > (α univ).toReal * (m + 1) + 1
  obtain ⟨N, hN⟩ := exists_nat_gt ((α Set.univ).toReal * ((m : ℝ) + 1))
  obtain ⟨s, hs_sub, hs_card⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
  have hsum : ∑ x ∈ s, α {x} ≤ α Set.univ := by
    rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)
          (fun _ _ => measurableSet_singleton _)]
    exact measure_mono (subset_univ _)
  have hlow : ((N + 1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / (m + 1 : ℕ)) ≤ ∑ x ∈ s, α {x} := by
    calc ((N + 1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / (m + 1 : ℕ))
        = ∑ _x ∈ s, ((1 : ℝ≥0∞) / (m + 1 : ℕ)) := by simp [hs_card]
      _ ≤ ∑ x ∈ s, α {x} := Finset.sum_le_sum fun x hx => hs_sub hx
  have hle := hlow.trans hsum
  have htr : (((N + 1 : ℕ) : ℝ) / ((m : ℝ) + 1)) ≤ (α Set.univ).toReal := by
    have hfin1 : ((N + 1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / (m + 1 : ℕ)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
      exact ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
    have := ENNReal.toReal_mono (measure_ne_top α _) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast] at this
    simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using this
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have : ((N : ℝ) + 1) ≤ (α Set.univ).toReal * ((m : ℝ) + 1) := by
    have := (div_le_iff₀ hpos).mp htr
    simpa [Nat.cast_add, Nat.cast_one] using this
  linarith

lemma exists_atom_free_in_Ioo (α : Measure ℝ) [IsFiniteMeasure α] {u v : ℝ} (huv : u < v) :
    ∃ x ∈ Set.Ioo u v, α {x} = 0 := by
  have hunc : ¬ (Set.Ioo u v).Countable := by
    intro hc
    have hcard : Cardinal.mk (Set.Ioo u v) ≤ Cardinal.aleph0 :=
      @Cardinal.mk_le_aleph0 (Set.Ioo u v) hc
    rw [Cardinal.mk_Ioo_real huv] at hcard
    exact not_le_of_gt Cardinal.aleph0_lt_continuum hcard
  have hne : (Set.Ioo u v \ {x : ℝ | α {x} ≠ 0}).Nonempty := by
    by_contra hempty
    have hsub : Set.Ioo u v ⊆ {x : ℝ | α {x} ≠ 0} := by
      intro x hx
      by_contra hnot
      exact hempty ⟨x, hx, hnot⟩
    exact hunc ((countable_atoms α).mono hsub)
  obtain ⟨x, hx1, hx2⟩ := hne
  exact ⟨x, hx1, not_not.mp hx2⟩

lemma convergesInM_of_potential_tendsto {αs : ℕ → Measure ℝ} {α : Measure ℝ}
    (hαs : ∀ n, MartOT.Var.InM (αs n)) (hα : MartOT.Var.InM α)
    (hmass : ∀ n, αs n Set.univ = α Set.univ)
    (hpot : ∀ x : ℝ, Tendsto (fun n => MartOT.Var.potential (αs n) x) atTop (𝓝 (MartOT.Var.potential α x))) :
    MartOT.Shadow.ConvergesInM αs α := by
  have : IsFiniteMeasure α := hα.1
  have : ∀ n, IsFiniteMeasure (αs n) := fun n => (hαs n).1
  refine ⟨hαs, hα, ?_, ?_⟩
  · intro f
    rw [Metric.tendsto_atTop]
    intro ε hε
    set M : ℝ := ‖f‖ + 1
    have hM : 0 < M := by positivity
    have hf_le : ∀ x : ℝ, |f x| ≤ M := fun x =>
      (Real.norm_eq_abs (f x) ▸ f.norm_coe_le_norm x).trans (by linarith)
    set k : ℝ := (α Set.univ).toReal
    have hk : 0 ≤ k := ENNReal.toReal_nonneg
    set η : ℝ := ε / (2 * k + 4 * M + 2)
    have hη : 0 < η := div_pos hε (by positivity)
    -- Tail bounds: pick continuity points a < b with small tails
    have hbot_tend : Tendsto (fun x : ℝ => (α (Set.Iic x)).toReal) atBot (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => α (Set.Iic x)) atBot (𝓝 0) := by
        have : Tendsto (fun n : ℕ => α (Set.Iic (-(n : ℝ)))) atTop (𝓝 (α (⋂ n : ℕ, Set.Iic (-(n : ℝ))))) :=
          tendsto_measure_iInter_atTop (fun _ => measurableSet_Iic.nullMeasurableSet)
            (fun _ _ h => Set.Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr h)))
            ⟨0, measure_ne_top α _⟩
        have hempty : (⋂ n : ℕ, Set.Iic (-(n : ℝ))) = ∅ := by
          ext x; simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
          obtain ⟨n, hn⟩ := exists_nat_gt (-x)
          exact ⟨n, by linarith⟩
        rw [hempty, measure_empty] at this
        rw [ENNReal.tendsto_atTop_zero] at this
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        obtain ⟨N, hN⟩ := this δ hδ
        filter_upwards [eventually_le_atBot (-(N : ℝ))] with x hx
        exact (measure_mono (Set.Iic_subset_Iic.mpr hx)).trans (hN N le_rfl)
      simpa [Function.comp_def] using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1
    have htop_tend : Tendsto (fun x : ℝ => (α (Set.Ioi x)).toReal) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x : ℝ => α (Set.Ioi x)) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => α (Set.Ioi (n : ℝ))) atTop (𝓝 (α (⋂ n : ℕ, Set.Ioi (n : ℝ)))) :=
          tendsto_measure_iInter_atTop (fun _ => measurableSet_Ioi.nullMeasurableSet)
            (fun _ _ h => Set.Ioi_subset_Ioi (Nat.cast_le.mpr h))
            ⟨0, measure_ne_top α _⟩
        have hempty : (⋂ n : ℕ, Set.Ioi (n : ℝ)) = ∅ := by
          ext x; simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false, not_forall, not_lt]
          obtain ⟨n, hn⟩ := exists_nat_gt x
          exact ⟨n, hn.le⟩
        rw [hempty, measure_empty] at this
        rw [ENNReal.tendsto_atTop_zero] at this
        rw [ENNReal.tendsto_nhds_zero]
        intro δ hδ
        obtain ⟨N, hN⟩ := this δ hδ
        filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
        exact (measure_mono (Set.Ioi_subset_Ioi hx)).trans (hN N le_rfl)
      simpa [Function.comp_def] using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1
    obtain ⟨a₀, ha₀⟩ := eventually_atBot.mp (hbot_tend (Iio_mem_nhds hη))
    obtain ⟨a, ha_Ioo, ha_atom⟩ := exists_atom_free_in_Ioo α (by linarith : a₀ - 1 < a₀)
    have ha_tail : (α (Set.Iic a)).toReal < η := ha₀ a ha_Ioo.2.le
    obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp (htop_tend (Iio_mem_nhds hη))
    set b₁ := max b₀ (a + 1)
    obtain ⟨b, hb_Ioo, hb_atom⟩ := exists_atom_free_in_Ioo α (by linarith : b₁ < b₁ + 1)
    have hab : a < b := by linarith [le_max_right b₀ (a + 1), hb_Ioo.1]
    have hb_tail : (α (Set.Ioi b)).toReal < η := hb₀ b (le_trans (le_max_left b₀ (a + 1)) hb_Ioo.1.le)
    -- Uniform continuity of f on [a, b]
    have huc : UniformContinuousOn f (Set.Icc a b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, huc_δ⟩ := huc η hη
    -- Build finite partition a = t 0 < t 1 < ... < t N = b of atom-free points with mesh < δ
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / (δ / 2))
    set N : ℕ := max N₀ 2
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    set h : ℝ := (b - a) / (N : ℝ)
    have hh_pos : 0 < h := div_pos (sub_pos.mpr hab) hN_pos
    have hh_lt : h < δ / 2 := by
      have hN₀_le : (N₀ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (le_max_left _ _)
      have h1 : (b - a) / (δ / 2) < (N : ℝ) := lt_of_lt_of_le hN₀ hN₀_le
      exact (div_lt_iff₀ hN_pos).mpr (by linarith [(div_lt_iff₀ (by linarith : 0 < δ / 2)).mp h1])
    have hex_pt : ∀ i : Fin (N + 1), ∃ x : ℝ,
        (i.val = 0 → x = a) ∧ (i.val = N → x = b) ∧
        (0 < i.val → i.val < N → x ∈ Set.Ioo (a + (i.val : ℝ) * h - h / 4) (a + (i.val : ℝ) * h + h / 4)) ∧
        α {x} = 0 := by
      intro i
      by_cases h0 : i.val = 0
      · exact ⟨a, fun _ => rfl, fun hN => by omega, fun h => by omega, ha_atom⟩
      · by_cases hN : i.val = N
        · exact ⟨b, fun h => by omega, fun _ => rfl, fun _ h => by omega, hb_atom⟩
        · obtain ⟨x, hx_Ioo, hx_atom⟩ :=
            exists_atom_free_in_Ioo α (by linarith : a + (i.val : ℝ) * h - h / 4 < a + (i.val : ℝ) * h + h / 4)
          exact ⟨x, fun h => by omega, fun h => by omega, fun _ _ => hx_Ioo, hx_atom⟩
    choose t ht0 htN ht_mid ht_atom using hex_pt
    have ht_approx : ∀ i : Fin (N + 1), |t i - (a + (i.val : ℝ) * h)| ≤ h / 4 := by
      intro i
      by_cases h0 : i.val = 0
      · rw [ht0 i h0, h0]; simp; linarith
      · by_cases hN : i.val = N
        · rw [htN i hN, hN]
          have : a + (N : ℝ) * h = b := by simp only [h]; field_simp [hN_pos.ne']; ring
          rw [this, sub_self, abs_zero]; linarith
        · have hi := ht_mid i (Nat.pos_of_ne_zero h0) (by omega)
          rw [abs_le]; constructor <;> linarith [hi.1, hi.2]
    have ht_step_lt : ∀ i : Fin N, t i.castSucc < t i.succ ∧ t i.succ - t i.castSucc < δ := by
      intro i
      have h1 := abs_le.mp (ht_approx i.castSucc)
      have h2 := abs_le.mp (ht_approx i.succ)
      have hcast : ((i.succ.val : ℝ) - (i.castSucc.val : ℝ)) = 1 := by simp
      have hdiff : (a + (i.succ.val : ℝ) * h) - (a + (i.castSucc.val : ℝ) * h) = h := by
        calc (a + (i.succ.val : ℝ) * h) - (a + (i.castSucc.val : ℝ) * h)
            = ((i.succ.val : ℝ) - (i.castSucc.val : ℝ)) * h := by ring
          _ = h := by rw [hcast, one_mul]
      constructor <;> linarith
    have ht_mono : Monotone t := by
      have haux : ∀ d : ℕ, ∀ i j : Fin (N + 1), j.val - i.val = d → i ≤ j → t i ≤ t j := by
        intro d
        induction d with
        | zero =>
          intro i j hd hij
          have : i = j := Fin.ext (by omega)
          subst this; exact le_rfl
        | succ d ih =>
          intro i j hd hij
          have hi_lt : i.val < N := by omega
          let i' : Fin (N + 1) := ⟨i.val + 1, by omega⟩
          have hstep : t i ≤ t i' := (ht_step_lt ⟨i.val, hi_lt⟩).1.le
          have hrest : t i' ≤ t j := ih i' j (by simp [i']; omega) (by show i'.val ≤ j.val; simp [i']; omega)
          exact hstep.trans hrest
      intro i j hij
      exact haux (j.val - i.val) i j rfl hij
    have ht_zero : t 0 = a := ht0 0 rfl
    have ht_last : t (Fin.last N) = b := htN (Fin.last N) rfl
    -- Define step function g
    let g : ℝ → ℝ := fun x =>
      ∑ i : Fin N, (Set.Ioc (t i.castSucc) (t i.succ)).indicator (fun _ => f (t i.succ)) x
    have hg_int : ∀ (γ : Measure ℝ), IsFiniteMeasure γ → Integrable g γ := fun γ _ =>
      integrable_finsetSum _ fun i _ => (integrable_const _).indicator measurableSet_Ioc
    -- Partition identity: on Ioc a b, unique interval contains x
    have hpart_disj : Pairwise fun i j : Fin N =>
        Disjoint (Set.Ioc (t i.castSucc) (t i.succ)) (Set.Ioc (t j.castSucc) (t j.succ)) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro x hxi hxj
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hle : t i.succ ≤ t j.castSucc := ht_mono (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hxi.2, hxj.1]
      · have hle : t j.succ ≤ t i.castSucc := ht_mono (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hxj.2, hxi.1]
    have hpart_union : (⋃ i : Fin N, Set.Ioc (t i.castSucc) (t i.succ)) = Set.Ioc a b := by
      ext x
      simp only [mem_iUnion, mem_Ioc]
      constructor
      · rintro ⟨i, h1, h2⟩
        exact ⟨lt_of_le_of_lt (ht_zero ▸ ht_mono (Fin.zero_le _)) h1,
               h2.trans (ht_last ▸ ht_mono (Fin.le_last _))⟩
      · rintro ⟨hax, hxb⟩
        -- Find first j such that x ≤ t j
        have hex : ∃ j : Fin (N + 1), x ≤ t j := ⟨Fin.last N, by rwa [ht_last]⟩
        let S : Finset (Fin (N + 1)) := Finset.univ.filter (fun j => x ≤ t j)
        have hSne : S.Nonempty := ⟨Fin.last N, by simp [S, ht_last, hxb]⟩
        let j := S.min' hSne
        have hj_mem : x ≤ t j := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
        have hj_ne0 : j.val ≠ 0 := by
          intro h0
          have : j = 0 := Fin.ext h0
          rw [this, ht_zero] at hj_mem
          linarith
        let i : Fin N := ⟨j.val - 1, by omega⟩
        have hi_succ : i.succ = j := Fin.ext (by simp [i]; omega)
        have hi_lt : t i.castSucc < x := by
          by_contra hle; push Not at hle
          have hmem : i.castSucc ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
          have hmin := Finset.min'_le S i.castSucc hmem
          change j ≤ i.castSucc at hmin
          have : j.val ≤ i.castSucc.val := hmin
          simp [i] at this; omega
        exact ⟨i, hi_lt, hi_succ ▸ hj_mem⟩
    -- Pointwise error bound |f x - g x|
    have herr_pt : ∀ x : ℝ, |f x - g x| ≤
        (Set.Ioc a b).indicator (fun _ => η) x +
        (Set.Iic a).indicator (fun _ => M) x +
        (Set.Ioi b).indicator (fun _ => M) x := by
      intro x
      by_cases hx : x ∈ Set.Ioc a b
      · have hx1 : x ∉ Set.Iic a := fun h => not_lt_of_ge (mem_Iic.mp h) hx.1
        have hx2 : x ∉ Set.Ioi b := fun h => not_le_of_gt (mem_Ioi.mp h) hx.2
        simp only [Set.indicator_of_mem hx, Set.indicator_of_notMem hx1, Set.indicator_of_notMem hx2, add_zero]
        rw [← hpart_union, mem_iUnion] at hx
        obtain ⟨i, hxi⟩ := hx
        have hg_eq : g x = f (t i.succ) := by
          dsimp only [g]
          rw [Finset.sum_eq_single i]
          · exact Set.indicator_of_mem hxi _
          · intro j _ hji
            exact Set.indicator_of_notMem (Set.disjoint_left.mp (hpart_disj hji.symm) hxi) _
          · intro hi; exact absurd (Finset.mem_univ i) hi
        rw [hg_eq]
        have hx_Icc : x ∈ Set.Icc a b :=
          ⟨(ht_zero ▸ ht_mono (Fin.zero_le i.castSucc)).trans hxi.1.le,
            hxi.2.trans (ht_last ▸ ht_mono (Fin.le_last i.succ))⟩
        have hti_Icc : t i.succ ∈ Set.Icc a b :=
          ⟨ht_zero ▸ ht_mono (Fin.zero_le i.succ), ht_last ▸ ht_mono (Fin.le_last i.succ)⟩
        have hdist : dist x (t i.succ) < δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxi.2)]
          linarith [hxi.1, (ht_step_lt i).2]
        exact (huc_δ x hx_Icc (t i.succ) hti_Icc hdist).le
      · have hg0 : g x = 0 := by
          dsimp only [g]
          refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun hi => hx ?_) _
          rw [← hpart_union]; exact mem_iUnion.mpr ⟨i, hi⟩
        rw [hg0, sub_zero, Set.indicator_of_notMem hx, zero_add]
        rcases le_or_gt x a with hxa | hxa
        · have hx2 : x ∉ Set.Ioi b := fun h => by linarith [mem_Ioi.mp h]
          simp only [Set.indicator_of_mem (mem_Iic.mpr hxa), Set.indicator_of_notMem hx2, add_zero]
          exact hf_le x
        · have hxb : b < x := by
            by_contra hle; push Not at hle; exact hx ⟨hxa, hle⟩
          have hx1 : x ∉ Set.Iic a := fun h => by linarith [mem_Iic.mp h]
          simp only [Set.indicator_of_notMem hx1, Set.indicator_of_mem (mem_Ioi.mpr hxb), zero_add]
          exact hf_le x
    -- Integral error bound for any finite measure γ with mass = α univ
    have herr_int : ∀ (γ : Measure ℝ) [IsFiniteMeasure γ], γ Set.univ = α Set.univ →
        |∫ x, f x ∂γ - ∫ x, g x ∂γ| ≤
          η * k + M * ((γ (Set.Iic a)).toReal + (γ (Set.Ioi b)).toReal) := by
      intro γ _ hγ_mass
      have hf_int : Integrable f γ := f.integrable γ
      have h1 : |∫ x, f x ∂γ - ∫ x, g x ∂γ| ≤ ∫ x, |f x - g x| ∂γ := by
        rw [← integral_sub hf_int (hg_int γ inferInstance)]
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x - g x)
      have hi1 : Integrable (fun x => (Set.Ioc a b).indicator (fun _ => η) x) γ :=
        (integrable_const η).indicator measurableSet_Ioc
      have hi2 : Integrable (fun x => (Set.Iic a).indicator (fun _ => M) x) γ :=
        (integrable_const M).indicator measurableSet_Iic
      have hi3 : Integrable (fun x => (Set.Ioi b).indicator (fun _ => M) x) γ :=
        (integrable_const M).indicator measurableSet_Ioi
      have hi12 : Integrable (fun x => (Set.Ioc a b).indicator (fun _ => η) x +
          (Set.Iic a).indicator (fun _ => M) x) γ := hi1.add hi2
      have h2 : ∫ x, |f x - g x| ∂γ ≤
          ∫ x, ((Set.Ioc a b).indicator (fun _ => η) x +
                (Set.Iic a).indicator (fun _ => M) x +
                (Set.Ioi b).indicator (fun _ => M) x) ∂γ :=
        integral_mono ((hf_int.sub (hg_int γ inferInstance)).norm) (hi12.add hi3) herr_pt
      have h3 : ∫ x, ((Set.Ioc a b).indicator (fun _ => η) x +
                (Set.Iic a).indicator (fun _ => M) x +
                (Set.Ioi b).indicator (fun _ => M) x) ∂γ =
          η * (γ (Set.Ioc a b)).toReal + M * ((γ (Set.Iic a)).toReal + (γ (Set.Ioi b)).toReal) := by
        rw [integral_add hi12 hi3, integral_add hi1 hi2,
            integral_indicator_const _ measurableSet_Ioc,
            integral_indicator_const _ measurableSet_Iic,
            integral_indicator_const _ measurableSet_Ioi]
        simp only [smul_eq_mul, Measure.real]; ring
      have h4 : (γ (Set.Ioc a b)).toReal ≤ k := by
        dsimp only [k]
        rw [← hγ_mass]
        exact ENNReal.toReal_mono (measure_ne_top γ _) (measure_mono (subset_univ _))
      calc |∫ x, f x ∂γ - ∫ x, g x ∂γ|
          ≤ η * (γ (Set.Ioc a b)).toReal + M * ((γ (Set.Iic a)).toReal + (γ (Set.Ioi b)).toReal) :=
            h1.trans (h2.trans_eq h3)
        _ ≤ η * k + M * ((γ (Set.Iic a)).toReal + (γ (Set.Ioi b)).toReal) := by
            gcongr
    -- Formula for ∫ g dγ
    have hg_eval : ∀ (γ : Measure ℝ) [IsFiniteMeasure γ],
        ∫ x, g x ∂γ = ∑ i : Fin N, f (t i.succ) * ((γ (Set.Iic (t i.succ))).toReal - (γ (Set.Iic (t i.castSucc))).toReal) := by
      intro γ _
      dsimp only [g]
      rw [integral_finsetSum _ fun i _ => (integrable_const _).indicator measurableSet_Ioc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, Measure.real, mul_comm]
      congr 1
      have hsub : Set.Iic (t i.castSucc) ⊆ Set.Iic (t i.succ) :=
        Set.Iic_subset_Iic.mpr (ht_step_lt i).1.le
      have hsdiff : Set.Ioc (t i.castSucc) (t i.succ) = Set.Iic (t i.succ) \ Set.Iic (t i.castSucc) := by
        ext x; simp [mem_Ioc]
      rw [hsdiff, measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (measure_ne_top γ _),
          ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top γ _)]
    -- Convergence of ∫ g d(αs n) → ∫ g dα and tails
    have hg_tend : Tendsto (fun n => ∫ x, g x ∂(αs n)) atTop (𝓝 (∫ x, g x ∂α)) := by
      simp_rw [hg_eval]
      refine tendsto_finsetSum _ fun i _ => ?_
      exact tendsto_const_nhds.mul
        ((cdf_tendsto_of_potential_tendsto hαs hα hmass hpot (ht_atom i.succ)).sub
         (cdf_tendsto_of_potential_tendsto hαs hα hmass hpot (ht_atom i.castSucc)))
    have ha_tend : Tendsto (fun n => (αs n (Set.Iic a)).toReal) atTop (𝓝 ((α (Set.Iic a)).toReal)) :=
      cdf_tendsto_of_potential_tendsto hαs hα hmass hpot ha_atom
    have hb_tend : Tendsto (fun n => (αs n (Set.Ioi b)).toReal) atTop (𝓝 ((α (Set.Ioi b)).toReal)) := by
      have hcomp : ∀ (γ : Measure ℝ) [IsFiniteMeasure γ],
          (γ (Set.Ioi b)).toReal = (γ Set.univ).toReal - (γ (Set.Iic b)).toReal := by
        intro γ _
        have : Set.Ioi b = Set.univ \ Set.Iic b := by ext x; simp
        rw [this, measure_sdiff (subset_univ _) measurableSet_Iic.nullMeasurableSet (measure_ne_top γ _),
            ENNReal.toReal_sub_of_le (measure_mono (subset_univ _)) (measure_ne_top γ _)]
      simp_rw [hcomp, hmass]
      exact tendsto_const_nhds.sub (cdf_tendsto_of_potential_tendsto hαs hα hmass hpot hb_atom)
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hg_tend η hη
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (ha_tend (Iio_mem_nhds ha_tail))
    obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (hb_tend (Iio_mem_nhds hb_tail))
    refine ⟨max N₁ (max N₂ N₃), fun n hn => ?_⟩
    have h1 := herr_int (αs n) (hmass n)
    have h2 := herr_int α rfl
    have h3 : |∫ x, g x ∂(αs n) - ∫ x, g x ∂α| < η := by
      simpa [Real.dist_eq] using hN₁ n (le_trans (le_max_left _ _) hn)
    have h4 : (αs n (Set.Iic a)).toReal < η := hN₂ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have h5 : (αs n (Set.Ioi b)).toReal < η := hN₃ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
    rw [Real.dist_eq]
    have htri : |∫ x, f x ∂(αs n) - ∫ x, f x ∂α| ≤
        |∫ x, f x ∂(αs n) - ∫ x, g x ∂(αs n)| +
        |∫ x, g x ∂(αs n) - ∫ x, g x ∂α| +
        |∫ x, g x ∂α - ∫ x, f x ∂α| := by
      calc |∫ x, f x ∂(αs n) - ∫ x, f x ∂α|
          = |(∫ x, f x ∂(αs n) - ∫ x, g x ∂(αs n)) +
              ((∫ x, g x ∂(αs n) - ∫ x, g x ∂α) + (∫ x, g x ∂α - ∫ x, f x ∂α))| := by ring_nf
        _ ≤ |∫ x, f x ∂(αs n) - ∫ x, g x ∂(αs n)| +
              |(∫ x, g x ∂(αs n) - ∫ x, g x ∂α) + (∫ x, g x ∂α - ∫ x, f x ∂α)| := abs_add_le _ _
        _ ≤ |∫ x, f x ∂(αs n) - ∫ x, g x ∂(αs n)| +
              (|∫ x, g x ∂(αs n) - ∫ x, g x ∂α| + |∫ x, g x ∂α - ∫ x, f x ∂α|) := by gcongr; exact abs_add_le _ _
        _ = _ := by ring
    rw [abs_sub_comm (∫ x, g x ∂α)] at htri
    have hbound : |∫ x, f x ∂(αs n) - ∫ x, f x ∂α| < η * (2 * k + 4 * M + 1) := by
      nlinarith
    have hlt : η * (2 * k + 4 * M + 1) < ε := by
      simp only [η]
      have hpos : (0 : ℝ) < 2 * k + 4 * M + 2 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
      nlinarith
    exact hbound.trans hlt
  · simpa [MartOT.Var.potential] using hpot 0

/-! ### Module 7: Convexity of pointwise limits and `StieltjesFunction` identity for `ν` -/

lemma convexOn_of_tendsto {fs : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hconv : ∀ n, ConvexOn ℝ Set.univ (fs n))
    (htend : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h1 := htend (a * x + b * y)
  have h2 := ((htend x).const_mul a).add ((htend y).const_mul b)
  exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => by
    simpa [smul_eq_mul] using (hconv n).2 trivial trivial ha hb hab)

lemma stieltjes_measure_eq_self {ν : Measure ℝ} (hν : MartOT.Var.InM ν) :
    (potentialStieltjes (MartOT.Var.potential ν) (potential_convexOn hν) (ν Set.univ).toReal).measure = ν := by
  have : IsFiniteMeasure ν := hν.1
  set F := potentialStieltjes (MartOT.Var.potential ν) (potential_convexOn hν) (ν Set.univ).toReal
  have hF_eq : ∀ x, F x = (ν (Set.Iic x)).toReal := by
    intro x
    change (rderiv (MartOT.Var.potential ν) x + (ν Set.univ).toReal) / 2 = _
    rw [potential_rderiv hν x]
    ring
  have hF_bot : Tendsto F atBot (𝓝 0) := by
    change Tendsto (fun x => F x) atBot (𝓝 0)
    simp_rw [hF_eq]
    have h1 : Tendsto (fun x : ℝ => ν (Set.Iic x)) atBot (𝓝 0) := by
      have : Tendsto (fun n : ℕ => ν (Set.Iic (-(n : ℝ)))) atTop (𝓝 (ν (⋂ n : ℕ, Set.Iic (-(n : ℝ))))) :=
        tendsto_measure_iInter_atTop (fun _ => measurableSet_Iic.nullMeasurableSet)
          (fun _ _ h => Set.Iic_subset_Iic.mpr (neg_le_neg (Nat.cast_le.mpr h)))
          ⟨0, measure_ne_top ν _⟩
      have hempty : (⋂ n : ℕ, Set.Iic (-(n : ℝ))) = ∅ := by
        ext x; simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
        obtain ⟨n, hn⟩ := exists_nat_gt (-x)
        exact ⟨n, by linarith⟩
      rw [hempty, measure_empty] at this
      rw [ENNReal.tendsto_atTop_zero] at this
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      obtain ⟨N, hN⟩ := this δ hδ
      filter_upwards [eventually_le_atBot (-(N : ℝ))] with x hx
      exact (measure_mono (Set.Iic_subset_Iic.mpr hx)).trans (hN N le_rfl)
    simpa [Function.comp_def] using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h1
  have hF_top : Tendsto F atTop (𝓝 (ν Set.univ).toReal) := by
    have htop_ν : Tendsto (fun x => MartOT.Var.potential ν x - ((ν Set.univ).toReal * x - ∫ y, y ∂ν))
        atTop (𝓝 0) := by
      simp_rw [potential_sub_right_asymptote hν]
      simpa using (tendsto_integral_max_sub_atTop hν).const_mul 2
    have h := rderiv_tendsto_atTop (potential_convexOn hν) htop_ν
    have h2 : Tendsto (fun x => (rderiv (MartOT.Var.potential ν) x + (ν Set.univ).toReal) / 2)
        atTop (𝓝 (((ν Set.univ).toReal + (ν Set.univ).toReal) / 2)) :=
      (h.add tendsto_const_nhds).div_const 2
    simpa [F, potentialStieltjes, add_halves] using h2
  have : IsFiniteMeasure F.measure := F.isFiniteMeasure hF_bot hF_top
  refine Measure.ext_of_Iic F.measure ν fun x => ?_
  rw [F.measure_Iic hF_bot x, sub_zero, hF_eq x, ENNReal.ofReal_toReal (measure_ne_top ν _)]

end Prop415Helpers

open Prop415Helpers

theorem solution (μs : ℕ → Measure ℝ) (μ ν : Measure ℝ)
    (hmono : ∀ n, MartOT.Var.ConvexLE (μs n) (μs (n + 1))) (hle : ∀ n, MartOT.Var.ConvexLE (μs n) μ)
    (hE : MartOT.Var.ExtConvexLE μ ν) (Ss : ℕ → Measure ℝ) (hS : ∀ n, MartOT.Var.IsShadow ν (μs n) (Ss n)) :
    ∃ μInf SInf : Measure ℝ, MartOT.Shadow.ConvergesInM μs μInf ∧ MartOT.Shadow.ConvergesInM Ss SInf ∧
      MartOT.Var.IsShadow ν μInf SInf := by
  have hμ : MartOT.Var.InM μ := (hle 0).2.1
  have hν : MartOT.Var.InM ν := hE.2.1
  have : IsFiniteMeasure μ := hμ.1
  have : IsFiniteMeasure ν := hν.1
  have hμs : ∀ n, MartOT.Var.InM (μs n) := fun n => (hle n).1
  have hSs : ∀ n, MartOT.Var.InM (Ss n) := fun n => (hS n).2.1.2.1
  set k : ℝ := (μ Set.univ).toReal
  have hk : 0 ≤ k := ENNReal.toReal_nonneg
  set m : ℝ := ∫ y, y ∂μ
  have hμs_mass : ∀ n, μs n Set.univ = μ Set.univ := fun n => convexLE_mass_eq (hle n)
  have hμs_mean : ∀ n, ∫ y, y ∂(μs n) = m := fun n => convexLE_mean_eq (hle n)
  have hSs_mass : ∀ n, Ss n Set.univ = μ Set.univ := fun n =>
    (convexLE_mass_eq (hS n).2.1).symm.trans (hμs_mass n)
  have hSs_mean : ∀ n, ∫ y, y ∂(Ss n) = m := fun n =>
    (convexLE_mean_eq (hS n).2.1).symm.trans (hμs_mean n)
  -- (Ss n) is increasing in ConvexLE
  have hS_mono : ∀ n, MartOT.Var.ConvexLE (Ss n) (Ss (n + 1)) := fun n =>
    (hS n).2.2 (Ss (n + 1)) (hS (n + 1)).1 (convexLE_trans (hmono n) (hS (n + 1)).2.1)
  -- Pointwise limits of potentials uμ and uS
  have hpot_μ_mono : ∀ x, Monotone (fun n => MartOT.Var.potential (μs n) x) := fun x =>
    monotone_nat_of_le_succ fun n => convexLE_potential_le (hmono n) x
  have hpot_μ_bdd : ∀ x, BddAbove (Set.range fun n => MartOT.Var.potential (μs n) x) := fun x =>
    ⟨MartOT.Var.potential μ x, by rintro _ ⟨n, rfl⟩; exact convexLE_potential_le (hle n) x⟩
  let uμ : ℝ → ℝ := fun x => ⨆ n, MartOT.Var.potential (μs n) x
  have huμ_tend : ∀ x, Tendsto (fun n => MartOT.Var.potential (μs n) x) atTop (𝓝 (uμ x)) := fun x =>
    tendsto_atTop_ciSup (hpot_μ_mono x) (hpot_μ_bdd x)
  have huμ_conv : ConvexOn ℝ Set.univ uμ :=
    convexOn_of_tendsto (fun n => potential_convexOn (hμs n)) huμ_tend
  have hpot_S_mono : ∀ x, Monotone (fun n => MartOT.Var.potential (Ss n) x) := fun x =>
    monotone_nat_of_le_succ fun n => convexLE_potential_le (hS_mono n) x
  have hpot_S_le_ν : ∀ n x, MartOT.Var.potential (Ss n) x ≤ MartOT.Var.potential ν x := fun n x =>
    integral_mono_measure (hS n).1 (ae_of_all _ fun _ => abs_nonneg _) (inM_integrable_abs_sub hν x)
  have hpot_S_bdd : ∀ x, BddAbove (Set.range fun n => MartOT.Var.potential (Ss n) x) := fun x =>
    ⟨MartOT.Var.potential ν x, by rintro _ ⟨n, rfl⟩; exact hpot_S_le_ν n x⟩
  let uS : ℝ → ℝ := fun x => ⨆ n, MartOT.Var.potential (Ss n) x
  have huS_tend : ∀ x, Tendsto (fun n => MartOT.Var.potential (Ss n) x) atTop (𝓝 (uS x)) := fun x =>
    tendsto_atTop_ciSup (hpot_S_mono x) (hpot_S_bdd x)
  have huS_conv : ConvexOn ℝ Set.univ uS :=
    convexOn_of_tendsto (fun n => potential_convexOn (hSs n)) huS_tend
  -- Asymptotes of uμ
  have huμ_top : Tendsto (fun x => uμ x - (k * x - m)) atTop (𝓝 0) := by
    have hlow : Tendsto (fun x => MartOT.Var.potential (μs 0) x - (k * x - m)) atTop (𝓝 0) := by
      have heq : (fun x => MartOT.Var.potential (μs 0) x - (k * x - m)) =
          (fun x => 2 * ∫ y, max (y - x) 0 ∂(μs 0)) := by
        ext x
        rw [show k = (μs 0 Set.univ).toReal by rw [hμs_mass 0],
            show m = ∫ y, y ∂(μs 0) by rw [hμs_mean 0]]
        exact potential_sub_right_asymptote (hμs 0) x
      rw [heq]
      simpa using (tendsto_integral_max_sub_atTop (hμs 0)).const_mul 2
    have hup : Tendsto (fun x => MartOT.Var.potential μ x - (k * x - m)) atTop (𝓝 0) := by
      have heq : (fun x => MartOT.Var.potential μ x - (k * x - m)) =
          (fun x => 2 * ∫ y, max (y - x) 0 ∂μ) := by
        ext x; exact potential_sub_right_asymptote hμ x
      rw [heq]
      simpa using (tendsto_integral_max_sub_atTop hμ).const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun x => ?_) (fun x => ?_)
    · exact sub_le_sub_right (le_ciSup (hpot_μ_bdd x) 0) _
    · exact sub_le_sub_right (ciSup_le fun n => convexLE_potential_le (hle n) x) _
  have huμ_bot : Tendsto (fun x => uμ x - (m - k * x)) atBot (𝓝 0) := by
    have hlow : Tendsto (fun x => MartOT.Var.potential (μs 0) x - (m - k * x)) atBot (𝓝 0) := by
      have heq : (fun x => MartOT.Var.potential (μs 0) x - (m - k * x)) =
          (fun x => 2 * ∫ y, max (x - y) 0 ∂(μs 0)) := by
        ext x
        rw [show k = (μs 0 Set.univ).toReal by rw [hμs_mass 0],
            show m = ∫ y, y ∂(μs 0) by rw [hμs_mean 0]]
        exact potential_sub_left_asymptote (hμs 0) x
      rw [heq]
      simpa using (tendsto_integral_max_sub_atBot (hμs 0)).const_mul 2
    have hup : Tendsto (fun x => MartOT.Var.potential μ x - (m - k * x)) atBot (𝓝 0) := by
      have heq : (fun x => MartOT.Var.potential μ x - (m - k * x)) =
          (fun x => 2 * ∫ y, max (x - y) 0 ∂μ) := by
        ext x; exact potential_sub_left_asymptote hμ x
      rw [heq]
      simpa using (tendsto_integral_max_sub_atBot hμ).const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun x => ?_) (fun x => ?_)
    · exact sub_le_sub_right (le_ciSup (hpot_μ_bdd x) 0) _
    · exact sub_le_sub_right (ciSup_le fun n => convexLE_potential_le (hle n) x) _
  -- Asymptotes of uS
  have huS_top : Tendsto (fun x => uS x - (k * x - m)) atTop (𝓝 0) := by
    have hup : Tendsto (fun x => 2 * ∫ y, max (y - x) 0 ∂ν) atTop (𝓝 0) := by
      simpa using (tendsto_integral_max_sub_atTop hν).const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun x => ?_) (fun x => ?_)
    · have h0 : 0 ≤ MartOT.Var.potential (Ss 0) x - (k * x - m) := by
        rw [show k = (Ss 0 Set.univ).toReal by rw [hSs_mass 0],
            show m = ∫ y, y ∂(Ss 0) by rw [hSs_mean 0],
            potential_sub_right_asymptote (hSs 0)]
        exact mul_nonneg (by norm_num) (integral_nonneg fun _ => le_max_right _ _)
      exact h0.trans (sub_le_sub_right (le_ciSup (hpot_S_bdd x) 0) _)
    · refine sub_le_iff_le_add.mpr (ciSup_le fun n => sub_le_iff_le_add.mp ?_)
      rw [show k = (Ss n Set.univ).toReal by rw [hSs_mass n],
          show m = ∫ y, y ∂(Ss n) by rw [hSs_mean n],
          potential_sub_right_asymptote (hSs n)]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure (hS n).1 (ae_of_all _ fun _ => le_max_right _ _) (integrable_max_sub_zero hν x))
        (by norm_num)
  have huS_bot : Tendsto (fun x => uS x - (m - k * x)) atBot (𝓝 0) := by
    have hup : Tendsto (fun x => 2 * ∫ y, max (x - y) 0 ∂ν) atBot (𝓝 0) := by
      simpa using (tendsto_integral_max_sub_atBot hν).const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun x => ?_) (fun x => ?_)
    · have h0 : 0 ≤ MartOT.Var.potential (Ss 0) x - (m - k * x) := by
        rw [show k = (Ss 0 Set.univ).toReal by rw [hSs_mass 0],
            show m = ∫ y, y ∂(Ss 0) by rw [hSs_mean 0],
            potential_sub_left_asymptote (hSs 0)]
        exact mul_nonneg (by norm_num) (integral_nonneg fun _ => le_max_right _ _)
      exact h0.trans (sub_le_sub_right (le_ciSup (hpot_S_bdd x) 0) _)
    · refine sub_le_iff_le_add.mpr (ciSup_le fun n => sub_le_iff_le_add.mp ?_)
      rw [show k = (Ss n Set.univ).toReal by rw [hSs_mass n],
          show m = ∫ y, y ∂(Ss n) by rw [hSs_mean n],
          potential_sub_left_asymptote (hSs n)]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure (hS n).1 (ae_of_all _ fun _ => le_max_right _ _) (integrable_max_zero_sub hν x))
        (by norm_num)
  -- Reconstruct μInf and SInf
  set Fμ := potentialStieltjes uμ huμ_conv k
  set FS := potentialStieltjes uS huS_conv k
  set μInf : Measure ℝ := Fμ.measure
  set SInf : Measure ℝ := FS.measure
  obtain ⟨hμInf_M, hμInf_univ, hμInf_mean, hμInf_pot⟩ :=
    measure_of_convex_props huμ_conv hk huμ_top huμ_bot
  obtain ⟨hSInf_M, hSInf_univ, hSInf_mean, hSInf_pot⟩ :=
    measure_of_convex_props huS_conv hk huS_top huS_bot
  have hμInf_mass : μInf Set.univ = μ Set.univ := by
    rw [hμInf_univ, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hSInf_mass : SInf Set.univ = μ Set.univ := by
    rw [hSInf_univ, ENNReal.ofReal_toReal (measure_ne_top μ _)]
  refine ⟨μInf, SInf, ?_, ?_, ?_, ?_, ?_⟩
  · -- ConvergesInM μs μInf
    refine convergesInM_of_potential_tendsto hμs hμInf_M
      (fun n => (hμs_mass n).trans hμInf_mass.symm)
      (fun x => by rw [hμInf_pot x]; exact huμ_tend x)
  · -- ConvergesInM Ss SInf
    refine convergesInM_of_potential_tendsto hSs hSInf_M
      (fun n => (hSs_mass n).trans hSInf_mass.symm)
      (fun x => by rw [hSInf_pot x]; exact huS_tend x)
  · -- IsShadow (i): SInf ≤ ν
    have hdiff_conv : ConvexOn ℝ Set.univ (fun x => MartOT.Var.potential ν x - uS x) :=
      convexOn_of_tendsto (fun n => potential_diff_convex_of_le hν (hS n).1)
        (fun x => tendsto_const_nhds.sub (huS_tend x))
    have hr_diff : ∀ x : ℝ, rderiv (fun y => MartOT.Var.potential ν y - uS y) x =
        rderiv (MartOT.Var.potential ν) x - rderiv uS x := by
      intro x
      have hd := (convexOn_hasDerivWithinAt_rderiv (potential_convexOn hν) x).sub
        (convexOn_hasDerivWithinAt_rderiv huS_conv x)
      exact hd.derivWithin (uniqueDiffWithinAt_Ioi x)
    set G := potentialStieltjes (fun y => MartOT.Var.potential ν y - uS y) hdiff_conv ((ν Set.univ).toReal - k)
    set Fν := potentialStieltjes (MartOT.Var.potential ν) (potential_convexOn hν) (ν Set.univ).toReal
    have hFG : FS + G = Fν := by
      ext x
      change (rderiv uS x + k) / 2 + (rderiv (fun y => MartOT.Var.potential ν y - uS y) x + ((ν Set.univ).toReal - k)) / 2 =
        (rderiv (MartOT.Var.potential ν) x + (ν Set.univ).toReal) / 2
      rw [hr_diff x]
      ring
    have hadd : SInf + G.measure = ν := by
      rw [← StieltjesFunction.measure_add, hFG, stieltjes_measure_eq_self hν]
    rw [← hadd]
    exact Measure.le_add_right le_rfl
  · -- IsShadow (ii): ConvexLE μInf SInf
    refine convexLE_of_potential_le hμInf_M hSInf_M (hμInf_mass.trans hSInf_mass.symm)
      (hμInf_mean.trans hSInf_mean.symm) fun x => ?_
    rw [hμInf_pot x, hSInf_pot x]
    exact le_of_tendsto_of_tendsto (huμ_tend x) (huS_tend x)
      (Eventually.of_forall fun n => convexLE_potential_le (hS n).2.1 x)
  · -- IsShadow (iii): ∀ η', η' ≤ ν → ConvexLE μInf η' → ConvexLE SInf η'
    intro η' hη'_le hη'_cvx
    have hη'_mass : SInf Set.univ = η' Set.univ :=
      hSInf_mass.trans (hμInf_mass.symm.trans (convexLE_mass_eq hη'_cvx))
    have hη'_mean : ∫ y, y ∂SInf = ∫ y, y ∂η' :=
      hSInf_mean.trans (hμInf_mean.symm.trans (convexLE_mean_eq hη'_cvx))
    refine convexLE_of_potential_le hSInf_M hη'_cvx.2.1 hη'_mass hη'_mean fun x => ?_
    rw [hSInf_pot x]
    refine ciSup_le fun n => ?_
    have hμn_le_μInf : MartOT.Var.ConvexLE (μs n) μInf :=
      convexLE_of_potential_le (hμs n) hμInf_M ((hμs_mass n).trans hμInf_mass.symm)
        ((hμs_mean n).trans hμInf_mean.symm)
        (fun y => by rw [hμInf_pot y]; exact le_ciSup (hpot_μ_bdd y) n)
    have hSn_le_η' : MartOT.Var.ConvexLE (Ss n) η' :=
      (hS n).2.2 η' hη'_le (convexLE_trans hμn_le_μInf hη'_cvx)
    exact convexLE_potential_le hSn_le_η' x
