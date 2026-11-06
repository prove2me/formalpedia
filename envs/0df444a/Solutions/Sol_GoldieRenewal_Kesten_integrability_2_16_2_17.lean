-- Prove2me | solution 1 for GoldieRenewal.Kesten.integrability_2_16_2_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:10:40.961199+00:00
-- url     : https://prove2.me/submissions/ad565205-8813-4dab-97ca-a067803b0878
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Kesten_RandomDifferenceEquation
import Definitions.Def_GoldieRenewal_Kesten_Perpetuity
import Theorems.Thm_GoldieRenewal_Kesten_eq_4_8
import Theorems.Thm_GoldieRenewal_Kesten_inequalities_9_26_9_27

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace KestenIntegAux

/-- Pointwise bound for `|(a⁺)^κ − (b⁺)^κ|` in the case `κ ≤ 1`. -/
lemma bound_le_one (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (a b : ℝ) :
    |(max a 0) ^ κ - (max b 0) ^ κ| ≤ |a - b| ^ κ := by
  have I := GoldieRenewal.Kesten.inequalities_9_26_9_27.2.1 (max a 0) (max b 0) κ hκ hκ1
  rw [abs_of_nonneg (le_max_right a 0), abs_of_nonneg (le_max_right b 0)] at I
  refine I.trans ?_
  apply Real.rpow_le_rpow (abs_nonneg _) (abs_max_sub_max_le_abs a b 0) hκ.le

/-- Pointwise bound for `|(a⁺)^κ − (b⁺)^κ|` in the case `κ > 1`. -/
lemma bound_gt_one (κ : ℝ) (hκ1 : 1 < κ) (a b : ℝ) :
    |(max a 0) ^ κ - (max b 0) ^ κ| ≤
      κ * max ((2 : ℝ) ^ (κ - 1 - 1)) 1 * (|a - b| ^ κ + |a - b| * |b| ^ (κ - 1)) := by
  have hk0 : 0 < κ - 1 := by linarith
  have I := GoldieRenewal.Kesten.inequalities_9_26_9_27.2.2 (max a 0) (max b 0) κ hκ1
  rw [abs_of_nonneg (le_max_right a 0), abs_of_nonneg (le_max_right b 0)] at I
  refine I.trans ?_
  set s := |a - b|
  set u := |b|
  have hs : 0 ≤ s := abs_nonneg _
  have hu : 0 ≤ u := abs_nonneg _
  have h1 : |max a 0 - max b 0| ≤ s := abs_max_sub_max_le_abs a b 0
  have h2 : max (max a 0) (max b 0) ≤ s + u := by
    have ha : max a 0 ≤ s + u := by
      apply max_le _ (by positivity)
      have : a = (a - b) + b := by ring
      calc a ≤ |a - b| + |b| := by
            rw [this]; exact (le_abs_self _).trans (abs_add_le _ _) |>.trans (by simp)
        _ = s + u := rfl
    have hb : max b 0 ≤ s + u := max_le ((le_abs_self b).trans (by linarith)) (by positivity)
    exact max_le ha hb
  have h3 : (max (max a 0) (max b 0)) ^ (κ - 1) ≤ (s + u) ^ (κ - 1) :=
    Real.rpow_le_rpow (le_max_of_le_left (le_max_right a 0)) h2 hk0.le
  have h4 : (s + u) ^ (κ - 1) ≤ max ((2 : ℝ) ^ (κ - 1 - 1)) 1 * (s ^ (κ - 1) + u ^ (κ - 1)) := by
    have := GoldieRenewal.Kesten.inequalities_9_26_9_27.1 s u (κ - 1) hk0
    rwa [abs_of_nonneg (by positivity : 0 ≤ s + u), abs_of_nonneg hs, abs_of_nonneg hu] at this
  have hss : s * s ^ (κ - 1) = s ^ κ := by
    rcases hs.lt_or_eq with hs' | hs'
    · rw [← Real.rpow_one_add' hs (ne_of_gt (by linarith))]; congr 1; ring
    · rw [← hs', Real.zero_rpow (by linarith), mul_zero, Real.zero_rpow (by linarith)]
  have hc : 0 ≤ max ((2 : ℝ) ^ (κ - 1 - 1)) 1 := le_max_of_le_right zero_le_one
  have hpow : 0 ≤ (max (max a 0) (max b 0)) ^ (κ - 1) :=
    Real.rpow_nonneg (le_max_of_le_left (le_max_right a 0)) _
  calc κ * |max a 0 - max b 0| * max (max a 0) (max b 0) ^ (κ - 1)
      ≤ κ * s * (max ((2 : ℝ) ^ (κ - 1 - 1)) 1 * (s ^ (κ - 1) + u ^ (κ - 1))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) (h3.trans h4) hpow
          (by positivity)
    _ = κ * max ((2 : ℝ) ^ (κ - 1 - 1)) 1 * (s * s ^ (κ - 1) + s * u ^ (κ - 1)) := by ring
    _ = κ * max ((2 : ℝ) ^ (κ - 1 - 1)) 1 * (s ^ κ + s * u ^ (κ - 1)) := by rw [hss]

/-- `|q| |m|^{κ-1} ≤ |q|^κ + |m|^κ` for `κ > 1`. -/
lemma young_like (κ : ℝ) (hκ1 : 1 < κ) (q m : ℝ) :
    |q| * |m| ^ (κ - 1) ≤ |q| ^ κ + |m| ^ κ := by
  have hq := abs_nonneg q
  have hm := abs_nonneg m
  have hk0 : 0 ≤ κ - 1 := by linarith
  have e : ∀ x : ℝ, 0 ≤ x → x * x ^ (κ - 1) = x ^ κ := by
    intro x hx
    rcases hx.lt_or_eq with hx' | hx'
    · rw [← Real.rpow_one_add' hx (ne_of_gt (by linarith))]; congr 1; ring
    · rw [← hx', Real.zero_rpow (by linarith), mul_zero, Real.zero_rpow (by linarith)]
  rcases le_total |q| |m| with h | h
  · have : |q| * |m| ^ (κ - 1) ≤ |m| * |m| ^ (κ - 1) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hm _)
    rw [e _ hm] at this
    linarith [Real.rpow_nonneg hq κ]
  · have : |q| * |m| ^ (κ - 1) ≤ |q| * |q| ^ (κ - 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm h hk0) hq
    rw [e _ hq] at this
    linarith [Real.rpow_nonneg hm κ]

end KestenIntegAux

open KestenIntegAux in
theorem solution (κ : ℝ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hM : GoldieRenewal.Implicit.CramerConditions κ (μ.map Prod.snd))
    (hQ : ∫⁻ p, ENNReal.ofReal (|p.1| ^ κ) ∂μ < ∞)
    (ρ : ProbabilityMeasure ℝ) (hρ : GoldieRenewal.Kesten.rdeOperator μ (ρ : Measure ℝ) = ρ) :
    Integrable (GoldieRenewal.Kesten.posDiff κ) (μ.prod (ρ : Measure ℝ)) ∧
      Integrable (GoldieRenewal.Kesten.negDiff κ) (μ.prod (ρ : Measure ℝ)) := by
  have hκ : 0 < κ := hM.pos
  -- integrability of `|q|^κ` and `|m|^κ` under `μ`
  have hQi : Integrable (fun p : ℝ × ℝ => |p.1| ^ κ) μ := by
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1| ^ κ) μ := by
      apply Measurable.aestronglyMeasurable; fun_prop
    exact (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (abs_nonneg _) _)).1 hQ.ne
  have hMi : Integrable (fun p : ℝ × ℝ => |p.2| ^ κ) μ := by
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.2| ^ κ) μ := by
      apply Measurable.aestronglyMeasurable; fun_prop
    have h1 := hM.moment_eq_one
    rw [lintegral_map (by fun_prop) measurable_snd] at h1
    exact (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (abs_nonneg _) _)).1
      (by rw [h1]; exact ENNReal.one_ne_top)
  have hQp : Integrable (fun p : (ℝ × ℝ) × ℝ => |p.1.1| ^ κ) (μ.prod (ρ : Measure ℝ)) :=
    hQi.comp_fst (ρ : Measure ℝ)
  have hmeasP : AEStronglyMeasurable (GoldieRenewal.Kesten.posDiff κ) (μ.prod (ρ : Measure ℝ)) := by
    apply Measurable.aestronglyMeasurable
    unfold GoldieRenewal.Kesten.posDiff; fun_prop
  have hmeasN : AEStronglyMeasurable (GoldieRenewal.Kesten.negDiff κ) (μ.prod (ρ : Measure ℝ)) := by
    apply Measurable.aestronglyMeasurable
    unfold GoldieRenewal.Kesten.negDiff; fun_prop
  rcases le_or_gt κ 1 with hκ1 | hκ1
  · -- case `κ ≤ 1`: dominated by `|Q|^κ`
    constructor
    · refine hQp.mono' hmeasP (Filter.Eventually.of_forall fun p => ?_)
      have := bound_le_one κ hκ hκ1 (p.1.1 + p.1.2 * p.2) (p.1.2 * p.2)
      simp only [Real.norm_eq_abs, GoldieRenewal.Kesten.posDiff]
      simpa using this
    · refine hQp.mono' hmeasN (Filter.Eventually.of_forall fun p => ?_)
      have := bound_le_one κ hκ hκ1 (-(p.1.1 + p.1.2 * p.2)) (-(p.1.2 * p.2))
      simp only [Real.norm_eq_abs, GoldieRenewal.Kesten.negDiff]
      refine this.trans (le_of_eq ?_)
      congr 1
      rw [show -(p.1.1 + p.1.2 * p.2) - -(p.1.2 * p.2) = -p.1.1 by ring, abs_neg]
  · -- case `κ > 1`: uses `E|R|^{κ-1} < ∞` from (4.8)
    have hR := (GoldieRenewal.Kesten.eq_4_8 κ μ hM hQ hκ1 ρ hρ).1
    set c := max ((2 : ℝ) ^ (κ - 1 - 1)) 1
    have hprod : Integrable (fun p : (ℝ × ℝ) × ℝ => (|p.1.1| ^ κ + |p.1.2| ^ κ) * |p.2| ^ (κ - 1))
        (μ.prod (ρ : Measure ℝ)) := (hQi.add hMi).mul_prod hR
    have hdom : Integrable (fun p : (ℝ × ℝ) × ℝ =>
        κ * c * (|p.1.1| ^ κ + (|p.1.1| ^ κ + |p.1.2| ^ κ) * |p.2| ^ (κ - 1)))
        (μ.prod (ρ : Measure ℝ)) := (hQp.add hprod).const_mul (κ * c)
    have hc : 0 ≤ κ * c := mul_nonneg hκ.le (le_max_of_le_right zero_le_one)
    have key : ∀ (q m r : ℝ) (a b : ℝ), |a - b| = |q| → |b| = |m| * |r| →
        |(max a 0) ^ κ - (max b 0) ^ κ| ≤
          κ * c * (|q| ^ κ + (|q| ^ κ + |m| ^ κ) * |r| ^ (κ - 1)) := by
      intro q m r a b hab hb
      refine (bound_gt_one κ hκ1 a b).trans ?_
      rw [hab, hb, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ hc
      have hy := young_like κ hκ1 q m
      have hr : 0 ≤ |r| ^ (κ - 1) := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith
    constructor
    · refine hdom.mono' hmeasP (Filter.Eventually.of_forall fun p => ?_)
      simp only [Real.norm_eq_abs, GoldieRenewal.Kesten.posDiff]
      exact key p.1.1 p.1.2 p.2 _ _ (by congr 1; ring) (abs_mul _ _)
    · refine hdom.mono' hmeasN (Filter.Eventually.of_forall fun p => ?_)
      simp only [Real.norm_eq_abs, GoldieRenewal.Kesten.negDiff]
      exact key p.1.1 p.1.2 p.2 _ _
        (by rw [show -(p.1.1 + p.1.2 * p.2) - -(p.1.2 * p.2) = -p.1.1 by ring, abs_neg])
        (by rw [abs_neg, abs_mul])
