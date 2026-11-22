-- Prove2me | solution 1 for HardyLittlewoodMaximal.strongType_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:28:02.018081+00:00
-- url     : https://prove2.me/submissions/18e82f59-185b-4ddd-be6c-c9fc2c1b6222

import Mathlib
import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_HardyLittlewoodMaximal_weakType_one_one_euclidean

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_HardyLittlewoodMaximal_strongType_euclidean

open DbarRegularity

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

/-- For any measure on a pseudo-metric space, the measure of the open ball of a fixed radius is a
lower semicontinuous function of the centre. -/
theorem lowerSemicontinuous_measure_ball {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (r : ℝ) : LowerSemicontinuous fun x ↦ ν (ball x r) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  rw [Metric.isOpen_iff]
  intro x hx
  -- The ball is the increasing union of the concentric balls of radii `r - 1/(n+1)`.
  have hunion : ball x r = ⋃ n : ℕ, ball x (r - 1 / ((n : ℝ) + 1)) := by
    ext y
    simp only [Set.mem_iUnion, mem_ball]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ ↦ ball x (r - 1 / ((n : ℝ) + 1)) := by
    intro n m hnm
    apply ball_subset_ball
    have h1 : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hx' : a < ν (ball x r) := hx
  rw [hunion, hmono.measure_iUnion] at hx'
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hx'
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun x' hx' ↦ ?_⟩
  refine hn.trans_le (measure_mono fun y hy ↦ ?_)
  rw [mem_ball] at hy hx' ⊢
  have h3 := dist_triangle y x x'
  rw [dist_comm x x'] at h3
  linarith

/-- The Hardy–Littlewood maximal function of an arbitrary function is lower semicontinuous. -/
theorem lowerSemicontinuous_maximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    LowerSemicontinuous (maximalFunction f) := by
  let ν : Measure (EuclideanSpace ℝ (Fin d)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity (fun y ↦ ‖f y‖ₑ)
  have hfun : maximalFunction f = fun x ↦ ⨆ (r : ℝ) (_ : 0 < r),
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) r))⁻¹ * ν (ball x r) := by
    funext x
    unfold maximalFunction
    refine iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
    rw [Measure.addHaar_ball_center volume x r]
    exact congrArg _ (withDensity_apply _ measurableSet_ball).symm
  rw [hfun]
  refine lowerSemicontinuous_iSup fun r ↦ lowerSemicontinuous_iSup fun hr ↦ ?_
  have hc : (volume (ball (0 : EuclideanSpace ℝ (Fin d)) r))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (measure_ball_pos volume _ hr).ne'
  exact (ENNReal.continuous_const_mul hc).comp_lowerSemicontinuous
    (lowerSemicontinuous_measure_ball ν r) (fun a b hab ↦ mul_le_mul' le_rfl hab)

theorem measurable_maximalFunction {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    Measurable (maximalFunction f) :=
  (lowerSemicontinuous_maximalFunction f).measurable

/-- Truncation at height `t`: the superlevel set `{Mf > 2t}` is controlled by the part of `f`
above `t`. -/
theorem tail {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal (2 * t) < maximalFunction f x} ≤
      ENNReal.ofReal (3 ^ d / t) * ∫⁻ x in {x | ENNReal.ofReal t < ‖f x‖ₑ}, ‖f x‖ₑ := by
  classical
  let s : Set (EuclideanSpace ℝ (Fin d)) := {x | ENNReal.ofReal t < ‖f x‖ₑ}
  let g := s.indicator f
  have hs : MeasurableSet s := measurableSet_lt measurable_const hf.enorm
  have ht₀ : ENNReal.ofReal t ≠ 0 := by simp [ht]
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  -- The set where `|f| > t` has finite measure (Chebyshev), so `g = f 1_{|f| > t}` is integrable.
  have hsFin : volume s ≠ ∞ := by
    apply (measure_mono (fun x (hx : x ∈ s) ↦ (show ENNReal.ofReal t < ‖f x‖ₑ from hx).le)).trans_lt
      (hLp.meas_ge_lt_top'_enorm hp0 ENNReal.ofReal_ne_top ht₀ (by simp)) |>.ne
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hLp.indicator hs
  have hg : Integrable g volume := memLp_one_iff_integrable.mp
    (hgLp.mono_exponent_of_measure_support_ne_top
      (fun x hx ↦ Set.indicator_of_notMem hx f) hsFin hp₁)
  have hnorm (y : EuclideanSpace ℝ (Fin d)) : ‖f y‖ₑ ≤ ‖g y‖ₑ + ENNReal.ofReal t := by
    by_cases hy : y ∈ s
    · simp [g, hy]
    · simpa [g, hy] using le_of_not_gt (show ¬ ENNReal.ofReal t < ‖f y‖ₑ from hy)
  -- Pointwise `Mf ≤ Mg + t`.
  have hmax (x : EuclideanSpace ℝ (Fin d)) :
      maximalFunction f x ≤ maximalFunction g x + ENNReal.ofReal t := by
    unfold maximalFunction
    refine iSup₂_le fun r hr ↦ ?_
    have hv0 : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
    have hvtop : volume (ball x r) ≠ ∞ := measure_ball_lt_top.ne
    have hcancel : (volume (ball x r))⁻¹ * (ENNReal.ofReal t * volume (ball x r)) =
        ENNReal.ofReal t := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hv0 hvtop, mul_one]
    calc (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
        ≤ (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, (‖g y‖ₑ + ENNReal.ofReal t) := by
          gcongr
          exact hnorm _
      _ = (volume (ball x r))⁻¹ * (∫⁻ y in ball x r, ‖g y‖ₑ) + ENNReal.ofReal t := by
          rw [lintegral_add_left' hg.aestronglyMeasurable.enorm.restrict, setLIntegral_const,
            mul_add, hcancel]
      _ ≤ _ := by
          gcongr
          exact le_iSup₂ (f := fun (r : ℝ) (_ : 0 < r) ↦
            (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖g y‖ₑ) r hr
  have hsubset : {x | ENNReal.ofReal (2 * t) < maximalFunction f x} ⊆
      {x | ENNReal.ofReal t < maximalFunction g x} := by
    intro x hx
    change ENNReal.ofReal (2 * t) < maximalFunction f x at hx
    rw [two_mul, ENNReal.ofReal_add ht.le ht.le] at hx
    change ENNReal.ofReal t < maximalFunction g x
    by_contra hcon
    have h : maximalFunction g x ≤ ENNReal.ofReal t := not_lt.mp hcon
    exact (hx.trans_le ((hmax x).trans (add_le_add h le_rfl))).false
  refine (measure_mono hsubset).trans ?_
  -- Weak type `(1,1)` inequality with constant `3^d`, applied to `g` at height `t`.
  have hweak : volume {x | ENNReal.ofReal t < maximalFunction g x} ≤
      ENNReal.ofReal (3 ^ d / t) * ∫⁻ x, ‖g x‖ₑ :=
    HardyLittlewoodMaximal.weakType_one_one_euclidean d g hg t ht
  have hgint : (∫⁻ x, ‖g x‖ₑ) = ∫⁻ x in s, ‖f x‖ₑ := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun x ↦ ?_
    exact enorm_indicator_eq_indicator_enorm f x
  rwa [hgint] at hweak

/-- The strong type inequality for a measurable function. -/
theorem strong_measurable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℂ} (hf : Measurable f) {p : ℝ}
    (hp : 1 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, maximalFunction f x ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p * 3 ^ d * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := sub_pos.mpr hp
  let M (x : EuclideanSpace ℝ (Fin d)) := maximalFunction f x / 2
  have hM : Measurable M := (measurable_maximalFunction f).div_const 2
  -- The weighted measure `ν = |f| dx` accounts for the factor `|f|` in the tail estimate.
  let ν := (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity (fun x ↦ ‖f x‖ₑ)
  have htail (t : ℝ) (ht : 0 < t) :
      volume {x | ENNReal.ofReal t < M x} ≤
        ENNReal.ofReal (3 ^ d / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ} := by
    have hlevel : {x | ENNReal.ofReal t < M x} =
        {x | ENNReal.ofReal (2 * t) < maximalFunction f x} := by
      ext x
      change ENNReal.ofReal t < maximalFunction f x / 2 ↔
        ENNReal.ofReal (2 * t) < maximalFunction f x
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
        two_mul, ENNReal.ofReal_add ht.le ht.le, mul_two]
    rw [hlevel, withDensity_apply']
    exact tail hf hp hLp ht
  -- Layer-cake formula for `|f|^{p-1}` with respect to `ν`.
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
  have hrescale (x : EuclideanSpace ℝ (Fin d)) : maximalFunction f x ^ p =
      ENNReal.ofReal ((2 : ℝ) ^ p) * M x ^ p := by
    have h : 2 * M x = maximalFunction f x := by
      rw [mul_comm]
      exact ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc
      maximalFunction f x ^ p = (2 * M x) ^ p := by rw [h]
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
        (ENNReal.ofReal (3 ^ d) *
          ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < ‖f x‖ₑ} *
            ENNReal.ofReal (t ^ (p - 2))) := by
      gcongr
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
      have ht' : 0 < t := ht
      have hweight : ENNReal.ofReal (3 ^ d / t) * ENNReal.ofReal (t ^ (p - 1)) =
          ENNReal.ofReal (3 ^ d) * ENNReal.ofReal (t ^ (p - 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 ^ d / t),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 ^ d)]
        congr 1
        rw [show t ^ (p - 2) = t ^ (p - 1) / t by
          rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub ht', Real.rpow_one]]
        ring
      calc
        volume {x | ENNReal.ofReal t < M x} * ENNReal.ofReal (t ^ (p - 1))
            ≤ (ENNReal.ofReal (3 ^ d / t) * ν {x | ENNReal.ofReal t < ‖f x‖ₑ}) *
            ENNReal.ofReal (t ^ (p - 1)) := by gcongr; exact htail t ht'
        _ = _ := by rw [mul_right_comm, hweight, mul_right_comm, mul_assoc]
    _ = _ := by
      have h := congrArg (fun a ↦ (ENNReal.ofReal (p - 1))⁻¹ * a) hweighted
      rw [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hp₁)
        ENNReal.ofReal_ne_top] at h
      rw [h, show (2 : ℝ) ^ p * 3 ^ d * p / (p - 1) =
        ((2 : ℝ) ^ p * p) * (3 ^ d * (p - 1)⁻¹) by ring,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p * p),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ p),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 ^ d),
        ENNReal.ofReal_inv_of_pos hp₁]
      simp only [mul_assoc]

/-- The maximal function only depends on the almost-everywhere class of `f`. -/
theorem maximalFunction_congr {d : ℕ} {f g : EuclideanSpace ℝ (Fin d) → ℂ}
    (h : f =ᵐ[volume] g) (x : EuclideanSpace ℝ (Fin d)) :
    maximalFunction f x = maximalFunction g x := by
  have hae : (fun y ↦ ‖f y‖ₑ) =ᵐ[volume] fun y ↦ ‖g y‖ₑ := h.fun_comp (‖·‖ₑ)
  unfold maximalFunction
  refine iSup_congr fun r ↦ iSup_congr fun _ ↦ ?_
  rw [lintegral_congr_ae (ae_restrict_of_ae hae)]

end Sol_HardyLittlewoodMaximal_strongType_euclidean

open Sol_HardyLittlewoodMaximal_strongType_euclidean in
theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∫⁻ x, DbarRegularity.maximalFunction f x ^ p ≤
      ENNReal.ofReal (2 ^ p * 3 ^ d * p / (p - 1)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  -- Replace `f` by a strongly measurable representative of its class.
  obtain ⟨g, hg, hfg⟩ := hf.aestronglyMeasurable
  have hgLp : MemLp g (ENNReal.ofReal p) volume := hf.ae_eq hfg
  have hstrong := strong_measurable hg.measurable hp hgLp
  have hleft : (∫⁻ x, DbarRegularity.maximalFunction f x ^ p) =
      ∫⁻ x, DbarRegularity.maximalFunction g x ^ p :=
    lintegral_congr fun x ↦ congrArg (· ^ p) (maximalFunction_congr hfg x)
  have hright : (∫⁻ x, ‖f x‖ₑ ^ p) = ∫⁻ x, ‖g x‖ₑ ^ p :=
    lintegral_congr_ae (hfg.fun_comp (fun z : ℂ ↦ ‖z‖ₑ ^ p))
  rw [hleft, hright]
  exact hstrong
