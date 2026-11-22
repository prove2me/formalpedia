-- Prove2me | solution 1 for HardyLittlewoodMaximal.strongType_real
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:23:38.535808+00:00
-- url     : https://prove2.me/submissions/92f5f806-a54d-45ea-9c7e-223928945700

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_HardyLittlewoodMaximal_strongType_real

/-- The centred Hardy–Littlewood maximal function on the real line. -/
noncomputable def maximal (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r),
    (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)

/-- Layer-cake formula for a positive real power of an extended nonnegative function. -/
theorem lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} *
        ENNReal.ofReal (t ^ (p - 1)) := by
  let trunc (n : ℕ) (x : α) := f x ⊓ (n : ℝ≥0∞)
  let tail (g : α → ℝ≥0∞) (t : ℝ) :=
    μ {x | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1))
  have hmono : Monotone trunc := fun n m hnm x ↦ inf_le_inf_left _ (Nat.cast_le.mpr hnm)
  have hmeas (n : ℕ) : AEMeasurable (trunc n) μ := hf.inf aemeasurable_const
  have htrunc (n : ℕ) (x : α) : ENNReal.ofReal (trunc n x).toReal = trunc n x :=
    ENNReal.ofReal_toReal ((inf_le_right : trunc n x ≤ (n : ℝ≥0∞)).trans_lt
      (ENNReal.natCast_lt_top n)).ne
  have hformula (n : ℕ) : (∫⁻ x, trunc n x ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), tail (trunc n) t := by
    calc
      (∫⁻ x, trunc n x ^ p ∂μ) = ∫⁻ x, ENNReal.ofReal ((trunc n x).toReal ^ p) ∂μ := by
        apply lintegral_congr
        intro x
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, htrunc]
      _ = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < (trunc n x).toReal} *
          ENNReal.ofReal (t ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) (hmeas n).ennreal_toReal hp
      _ = _ := by
        refine congrArg (ENNReal.ofReal p * ·) (lintegral_congr_ae ?_)
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
        dsimp only [tail]
        congr 2
        ext x
        change (t < (trunc n x).toReal ↔ ENNReal.ofReal t < trunc n x)
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).symm.trans
          (by rw [htrunc])
  have hs (x : α) : (⨆ n, trunc n x) = f x := by
    simp only [trunc, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have htail (n : ℕ) : Measurable (tail (trunc n)) := by
    have hanti : Antitone (fun t : ℝ ↦ μ {x | ENNReal.ofReal t < trunc n x}) :=
      fun _ _ hab ↦ measure_mono fun _ hx ↦ (ENNReal.ofReal_le_ofReal hab).trans_lt hx
    exact hanti.measurable.mul (by fun_prop)
  have htail_mono {g₁ g₂ : α → ℝ≥0∞} (h : g₁ ≤ g₂) (t : ℝ) : tail g₁ t ≤ tail g₂ t := by
    have hs : {x | ENNReal.ofReal t < g₁ x} ⊆ {x | ENNReal.ofReal t < g₂ x} :=
      fun x hx ↦ (show ENNReal.ofReal t < g₁ x from hx).trans_le (h x)
    dsimp only [tail]
    gcongr
  have htailMono : Monotone (fun n ↦ tail (trunc n)) := fun _ _ h t ↦ htail_mono (hmono h) t
  have htailSup (t : ℝ) : (⨆ n, tail (trunc n) t) = tail f t := by
    refine le_antisymm (iSup_le fun n ↦ htail_mono (fun x ↦ inf_le_left) t) ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.ofReal_ne_top (r := t))
    have heq : tail (trunc n) t = tail f t := by
      simp only [tail, trunc, lt_inf_iff, hn, and_true]
    exact heq ▸ le_iSup (fun n ↦ tail (trunc n) t) n
  have hpow (x : α) : f x ^ p = ⨆ n, trunc n x ^ p := by
    have h := (ENNReal.orderIsoRpow p hp).map_iSup (fun n ↦ trunc n x)
    simpa only [ENNReal.orderIsoRpow_apply, hs] using h
  change (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0 : ℝ), tail f t
  simp_rw [hpow]
  rw [lintegral_iSup' (fun n ↦ (hmeas n).pow_const p) (Filter.Eventually.of_forall fun x _ _ hnm ↦
    ENNReal.rpow_le_rpow (hmono hnm x) hp.le)]
  simp_rw [hformula, ← ENNReal.mul_iSup]
  rw [← lintegral_iSup htail htailMono]
  exact congrArg (ENNReal.ofReal p * ·) (lintegral_congr htailSup)

/-- The maximal function of a locally integrable function is lower semicontinuous,
hence measurable. -/
theorem measurable_maximal {f : ℝ → ℂ} (hlocal : LocallyIntegrable f volume) :
    Measurable (maximal f) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun y ↦ ‖f y‖) volume a b :=
    (IntegrableOn.intervalIntegrable
      (hlocal.integrableOn_isCompact (k := Set.uIcc a b) isCompact_uIcc)).norm
  have hprimitive := intervalIntegral.continuous_primitive hint 0
  apply LowerSemicontinuous.measurable
  unfold maximal
  refine lowerSemicontinuous_iSup fun r ↦ lowerSemicontinuous_iSup fun hr ↦ ?_
  apply Continuous.lowerSemicontinuous
  have havg : Continuous (fun x : ℝ ↦ ∫ y in x - r..x + r, ‖f y‖) := by
    have hright : Continuous (fun x : ℝ ↦ x + r) := continuous_id.add continuous_const
    have hleft : Continuous (fun x : ℝ ↦ x - r) := continuous_id.sub continuous_const
    convert (hprimitive.comp hright).sub (hprimitive.comp hleft) using 1
    ext x
    exact (intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)).symm
  have hlintegral (x : ℝ) :
      (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) =
        ENNReal.ofReal (∫ y in x - r..x + r, ‖f y‖) := by
    have hab : x - r ≤ x + r := by linarith
    rw [intervalIntegral.integral_of_le hab,
      ofReal_integral_eq_lintegral_ofReal (hint _ _).1 (Eventually.of_forall fun y ↦ norm_nonneg _)]
    simp only [ofReal_norm]
    exact setLIntegral_congr Ioo_ae_eq_Ioc
  simp only [hlintegral]
  exact (ENNReal.continuous_div_const _ (by simp [hr])).comp
    (ENNReal.continuous_ofReal.comp havg)

/-- Weak type `(1,1)` with constant `3`. -/
theorem weak (f : ℝ → ℂ) (hf : Integrable f volume) (α : ℝ) (hα : 0 < α) :
    volume {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)} ≤
      ENNReal.ofReal (3 / α) * ∫⁻ x, ‖f x‖ₑ := by
  classical
  -- The measure `ν = |f| dx`; its total mass is the `L¹` norm of `f`.
  let ν : Measure ℝ := (volume : Measure ℝ).withDensity (fun x ↦ ‖f x‖ₑ)
  have hνapply : ∀ s : Set ℝ, MeasurableSet s → ν s = ∫⁻ y in s, ‖f y‖ₑ := fun s hs ↦
    withDensity_apply _ hs
  have hnorm : ν Set.univ = ∫⁻ x, ‖f x‖ₑ := by
    rw [hνapply _ MeasurableSet.univ, setLIntegral_univ]
  have htotal : ν Set.univ ≠ ∞ := by
    rw [hnorm]
    exact hf.hasFiniteIntegral.ne
  -- Intervals are indexed by (centre, radius).
  let interval : ℝ × ℝ → Set ℝ := fun p ↦ Set.Ioo (p.1 - p.2) (p.1 + p.2)
  let enlarged : ℝ × ℝ → Set ℝ := fun p ↦ Set.Icc (p.1 - 3 * p.2) (p.1 + 3 * p.2)
  -- The intervals on which the average of `|f|` exceeds `α`.
  let good : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ ENNReal.ofReal (α * (2 * p.2)) < ν (interval p)}
  -- Their radii are bounded, because `ν` is a finite measure.
  have hbounded : ∀ p ∈ good, p.2 ≤ (ν Set.univ).toReal / α := by
    intro p hp
    have hpos : 0 < p.2 := hp.1
    have hle := ENNReal.toReal_mono htotal (hp.2.le.trans (measure_mono (Set.subset_univ _)))
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ α * (2 * p.2))] at hle
    rw [le_div_iff₀ hα]
    nlinarith [mul_nonneg hα.le hpos.le]
  -- Vitali selection: a disjoint subfamily such that every good interval meets a selected
  -- interval of at least half its radius.
  obtain ⟨u, hug, hdisjoint, hintersects⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement interval good Prod.snd 2
      one_lt_two (fun p hp ↦ hp.1.le) ((ν Set.univ).toReal / α) hbounded
      (fun p hp ↦ ⟨p.1, by
        change p.1 - p.2 < p.1 ∧ p.1 < p.1 + p.2
        have := hp.1
        constructor <;> linarith⟩)
  have hcount : u.Countable := hdisjoint.countable_of_isOpen (fun p _ ↦ isOpen_Ioo)
    (fun p hp ↦ by
      change (Set.Ioo (p.1 - p.2) (p.1 + p.2)).Nonempty
      exact Set.nonempty_Ioo.mpr (by linarith [(hug hp).1]))
  have : Countable u := hcount.to_subtype
  -- The superlevel set is covered by the threefold enlargements of the selected intervals.
  have hcover : {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)} ⊆
      ⋃ p : u, enlarged p.val := by
    intro x hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp (show ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r) from hx)
    obtain ⟨hr0, hr⟩ := lt_iSup_iff.mp hr
    have hgood : (x, r) ∈ good := by
      refine ⟨hr0, ?_⟩
      change ENNReal.ofReal (α * (2 * r)) < ν (Set.Ioo (x - r) (x + r))
      rw [hνapply _ measurableSet_Ioo, ENNReal.ofReal_mul hα.le]
      exact ENNReal.mul_lt_of_lt_div hr
    obtain ⟨p, hp, ⟨y, hy₁, hy₂⟩, hrad⟩ := hintersects (x, r) hgood
    refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    change x - r < y ∧ y < x + r at hy₁
    change p.1 - p.2 < y ∧ y < p.1 + p.2 at hy₂
    change r ≤ 2 * p.2 at hrad
    change p.1 - 3 * p.2 ≤ x ∧ x ≤ p.1 + 3 * p.2
    constructor <;> linarith [hy₁.1, hy₁.2, hy₂.1, hy₂.2]
  -- Each enlargement has length `6 r = (3/α) · (α · 2r) ≤ (3/α) ν(interval)`.
  have henlarged : ∀ p : u, volume (enlarged p.val) ≤
      ENNReal.ofReal (3 / α) * ν (interval p.val) := by
    intro p
    have hlength : p.val.1 + 3 * p.val.2 - (p.val.1 - 3 * p.val.2) =
        (3 / α) * (α * (2 * p.val.2)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hα.ne']
      ring
    change volume (Set.Icc (p.val.1 - 3 * p.val.2) (p.val.1 + 3 * p.val.2)) ≤ _
    rw [Real.volume_Icc, hlength, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl (hug p.property).2.le
  -- Disjointness: the selected intervals carry total `ν`-mass at most `ν(ℝ)`.
  have hsum : (∑' p : u, ν (interval p.val)) ≤ ν Set.univ := by
    rw [← measure_iUnion (hdisjoint.on_injective Subtype.val_injective Subtype.property)
      (fun _ ↦ measurableSet_Ioo)]
    exact measure_mono (Set.subset_univ _)
  calc
    volume {x : ℝ | ENNReal.ofReal α <
        ⨆ (r : ℝ) (_ : 0 < r),
          (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)}
        ≤ volume (⋃ p : u, enlarged p.val) := measure_mono hcover
    _ ≤ ∑' p : u, volume (enlarged p.val) := measure_iUnion_le _
    _ ≤ ∑' p : u, ENNReal.ofReal (3 / α) * ν (interval p.val) :=
        ENNReal.tsum_le_tsum henlarged
    _ = ENNReal.ofReal (3 / α) * ∑' p : u, ν (interval p.val) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (3 / α) * ν Set.univ := mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (3 / α) * ∫⁻ x, ‖f x‖ₑ := by rw [hnorm]

/-- Truncation at height `t`: the superlevel set `{Mf > 2t}` is controlled by the part of `f`
above `t`. -/
theorem tail {f : ℝ → ℂ} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal (2 * t) < maximal f x} ≤
      ENNReal.ofReal (3 / t) * ∫⁻ x in {x | ENNReal.ofReal t < ‖f x‖ₑ}, ‖f x‖ₑ := by
  classical
  let s : Set ℝ := {x | ENNReal.ofReal t < ‖f x‖ₑ}
  let g := s.indicator f
  have hs : MeasurableSet s := measurableSet_lt measurable_const hf.enorm
  have ht₀ : ENNReal.ofReal t ≠ 0 := by simp [ht]
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hsFin : volume s ≠ ∞ := by
    apply (measure_mono (fun x (hx : x ∈ s) ↦ (show ENNReal.ofReal t < ‖f x‖ₑ from hx).le)).trans_lt
      (hLp.meas_ge_lt_top'_enorm hp0 ENNReal.ofReal_ne_top ht₀ (by simp)) |>.ne
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hLp.indicator hs
  have hg : Integrable g volume := memLp_one_iff_integrable.mp
    (hgLp.mono_exponent_of_measure_support_ne_top
      (fun x hx ↦ Set.indicator_of_notMem hx f) hsFin hp₁)
  have hnorm (y : ℝ) : ‖f y‖ₑ ≤ ‖g y‖ₑ + ENNReal.ofReal t := by
    by_cases hy : y ∈ s
    · simp [g, hy]
    · simpa [g, hy] using le_of_not_gt (show ¬ ENNReal.ofReal t < ‖f y‖ₑ from hy)
  have hmax (x : ℝ) : maximal f x ≤ maximal g x + ENNReal.ofReal t := by
    unfold maximal
    refine iSup₂_le fun r hr ↦ ?_
    have hlen0 : ENNReal.ofReal (2 * r) ≠ 0 := by simp [hr]
    have hvol : volume (Set.Ioo (x - r) (x + r)) = ENNReal.ofReal (2 * r) := by
      rw [Real.volume_Ioo, show x + r - (x - r) = 2 * r by ring]
    calc (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)
        ≤ (∫⁻ y in Set.Ioo (x - r) (x + r), (‖g y‖ₑ + ENNReal.ofReal t)) /
            ENNReal.ofReal (2 * r) := by
          gcongr
          exact hnorm _
      _ = (∫⁻ y in Set.Ioo (x - r) (x + r), ‖g y‖ₑ) / ENNReal.ofReal (2 * r) +
            ENNReal.ofReal t := by
          rw [lintegral_add_left' hg.aestronglyMeasurable.enorm.restrict, setLIntegral_const,
            hvol, ENNReal.add_div, ENNReal.mul_div_cancel_right hlen0 ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) ↦
            (∫⁻ y in Set.Ioo (x - r) (x + r), ‖g y‖ₑ) / ENNReal.ofReal (2 * r)) r hr
  have hsubset : {x | ENNReal.ofReal (2 * t) < maximal f x} ⊆
      {x | ENNReal.ofReal t < maximal g x} := by
    intro x hx
    change ENNReal.ofReal (2 * t) < maximal f x at hx
    rw [two_mul, ENNReal.ofReal_add ht.le ht.le] at hx
    change ENNReal.ofReal t < maximal g x
    by_contra hcon
    have h : maximal g x ≤ ENNReal.ofReal t := not_lt.mp hcon
    exact (hx.trans_le ((hmax x).trans (add_le_add h le_rfl))).false
  refine (measure_mono hsubset).trans ?_
  have hweak : volume {x | ENNReal.ofReal t < maximal g x} ≤
      ENNReal.ofReal (3 / t) * ∫⁻ x, ‖g x‖ₑ := weak g hg t ht
  have hgint : (∫⁻ x, ‖g x‖ₑ) = ∫⁻ x in s, ‖f x‖ₑ := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun x ↦ ?_
    exact enorm_indicator_eq_indicator_enorm f x
  rwa [hgint] at hweak

/-- The strong type inequality for a measurable function. -/
theorem strong_measurable {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ}
    (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, maximal f x ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * 3 * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := sub_pos.mpr hp
  have hloc : LocallyIntegrable f volume :=
    hLp.locallyIntegrable (by simpa using ENNReal.ofReal_le_ofReal hp.le)
  let M (x : ℝ) := maximal f x / 2
  have hM : Measurable M := (measurable_maximal hloc).div_const 2
  -- Layer cake for this weighted measure accounts for the factor ‖f x‖ₑ in the tail.
  let ν := (volume : Measure ℝ).withDensity (fun x ↦ ‖f x‖ₑ)
  have htail (t : ℝ) (ht : 0 < t) :
      volume {x | ENNReal.ofReal t < M x} ≤
        ENNReal.ofReal (3 / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ} := by
    have hlevel : {x | ENNReal.ofReal t < M x} =
        {x | ENNReal.ofReal (2 * t) < maximal f x} := by
      ext x
      simp only [Set.mem_ofPred_eq, M, ENNReal.lt_div_iff_mul_lt (Or.inl two_ne_zero)
        (Or.inl ENNReal.ofNat_ne_top), two_mul, ENNReal.ofReal_add ht.le ht.le, mul_two]
    rw [hlevel, withDensity_apply']
    exact tail hf hp hLp ht
  have hweighted :
      ENNReal.ofReal (p - 1) * (∫⁻ t in Set.Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < ‖f x‖ₑ} *
        ENNReal.ofReal (t ^ (p - 2))) = ∫⁻ x, ‖f x‖ₑ ^ p := by
    have hfNorm : Measurable (fun x ↦ ‖f x‖ₑ) := hf.enorm
    have h := lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul ν
      (f := fun x ↦ ‖f x‖ₑ) hfNorm.aemeasurable hp₁
    rw [show p - 1 - 1 = p - 2 by ring] at h
    rw [← h, lintegral_withDensity_eq_lintegral_mul₀ hfNorm.aemeasurable
      (hfNorm.pow_const _).aemeasurable]
    refine lintegral_congr fun x ↦ ?_
    calc
      ((fun x ↦ ‖f x‖ₑ) * fun x ↦ ‖f x‖ₑ ^ (p - 1)) x
          = ‖f x‖ₑ ^ (1 : ℝ) * ‖f x‖ₑ ^ (p - 1) := by
        rw [Pi.mul_apply, ENNReal.rpow_one]
      _ = ‖f x‖ₑ ^ p := by
        rw [← ENNReal.rpow_add_of_nonneg 1 (p - 1) zero_le_one hp₁.le,
          show 1 + (p - 1) = p by ring]
  have hrescale (x : ℝ) : maximal f x ^ p =
      ENNReal.ofReal ((2 : ℝ) ^ p) * M x ^ p := by
    have h : 2 * M x = maximal f x := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc
      maximal f x ^ p = (2 * M x) ^ p := by rw [h]
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp₀.le,
          ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp₀.le,
          ENNReal.ofReal_ofNat]
  simp_rw [hrescale]
  rw [lintegral_const_mul _ (hM.pow_const p),
    lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul volume hM.aemeasurable hp₀, ← mul_assoc]
  calc
    ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal p *
        ∫⁻ t in Set.Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < M x} *
          ENNReal.ofReal (t ^ (p - 1))
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal p) *
        (3 * ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < ‖f x‖ₑ} *
          ENNReal.ofReal (t ^ (p - 2))) := by
      gcongr
      rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
      have ht' : 0 < t := ht
      have hweight : ENNReal.ofReal (3 / t) * ENNReal.ofReal (t ^ (p - 1)) =
          (3 : ℝ≥0∞) * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 / t), ← ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ))]
        congr 1
        rw [show t ^ (p - 2) = t ^ (p - 1) / t by
          rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub ht', Real.rpow_one]]
        ring
      calc
        volume {x | ENNReal.ofReal t < M x} * ENNReal.ofReal (t ^ (p - 1))
            ≤ (ENNReal.ofReal (3 / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ}) *
            ENNReal.ofReal (t ^ (p - 1)) := by gcongr; exact htail t ht'
        _ = _ := by rw [mul_right_comm, hweight, mul_right_comm, mul_assoc]
    _ = _ := by
      have h := congrArg (fun a ↦ (ENNReal.ofReal (p - 1))⁻¹ * a) hweighted
      rw [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hp₁)
        ENNReal.ofReal_ne_top] at h
      rw [h, show (2 : ℝ) ^ p * 3 * p / (p - 1) =
        ((2 : ℝ) ^ p * p) * (3 * (p - 1)⁻¹) by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p * p),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p),
        ENNReal.ofReal_mul (by norm_num : 0 ≤ (3 : ℝ)), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_inv_of_pos hp₁]
      simp only [mul_assoc]

/-- The maximal function only depends on the almost-everywhere class of `f`. -/
theorem maximal_congr {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) (x : ℝ) : maximal f x = maximal g x := by
  have hae : (fun y ↦ ‖f y‖ₑ) =ᵐ[volume] fun y ↦ ‖g y‖ₑ := h.fun_comp (‖·‖ₑ)
  unfold maximal
  refine iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
  rw [lintegral_congr_ae (ae_restrict_of_ae hae)]

end Sol_HardyLittlewoodMaximal_strongType_real

open Sol_HardyLittlewoodMaximal_strongType_real in
theorem solution (f : ℝ → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x : ℝ, (⨆ (r : ℝ) (_ : 0 < r),
        (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)) ^ p ≤
      ENNReal.ofReal (2 ^ p * 3 * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  -- Replace `f` by a strongly measurable representative of its class.
  obtain ⟨g, hg, hfg⟩ := hf.aestronglyMeasurable
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hf.ae_eq hfg
  have hstrong := strong_measurable hg.measurable hp hgLp
  have hleft : (∫⁻ x : ℝ, (⨆ (r : ℝ) (_ : 0 < r),
        (∫⁻ y in Set.Ioo (x - r) (x + r), ‖f y‖ₑ) / ENNReal.ofReal (2 * r)) ^ p) =
      ∫⁻ x, maximal g x ^ p :=
    lintegral_congr fun x ↦ congrArg (· ^ p) (maximal_congr hfg x)
  have hright : (∫⁻ x, ‖f x‖ₑ ^ p) = ∫⁻ x, ‖g x‖ₑ ^ p :=
    lintegral_congr_ae (hfg.fun_comp (fun z : ℂ ↦ ‖z‖ₑ ^ p))
  rw [hleft, hright]
  exact hstrong
