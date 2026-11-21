-- Prove2me | solution 1 for MasulloGRH.sobolev_window_jet_integrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:23:29.709497+00:00
-- url     : https://prove2.me/submissions/a9b31673-8834-459a-bf58-34c289b2b71e

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

private theorem integrable_even_of_pos (f : ℝ → ℝ) (heven : ∀ x, f (-x) = f x)
    (hpos : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hneg : IntegrableOn f (Iio 0) := by
    have hh := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hpos
    simpa [Function.comp_def, heven] using hh
  have hleft : IntegrableOn f (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio (by finiteness)).mpr hneg
  have hh := hleft.union hpos
  rwa [Iic_union_Ioi, integrableOn_univ] at hh

private theorem integrable_exp_abs_pow (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|) * x ^ (2 * m)) := by
  apply integrable_even_of_pos
  · intro x
    simp [pow_mul]
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 * m : ℕ)) (p := 1) (b := c) (by have := Nat.cast_nonneg (α := ℝ) (2 * m); linarith) (by norm_num) hc
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    simp only [Real.rpow_one, Real.rpow_natCast]
    rw [abs_of_pos hx]
    ring

private theorem weight_cont (m : ℕ) (s : ℝ) :
    Continuous (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) := by
  apply Continuous.div (by fun_prop)
  · apply Continuous.rpow_const (by fun_prop)
    intro x
    exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))
  · intro x
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)

theorem solution (m : ℕ) (s α b : ℝ) (hs : 1 < s) (hb : |b| ≤ α) :
    Integrable (fun x : ℝ => Real.exp (2 * b * x - 2 * α * |x|) *
      (x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2))) ↔
      |b| < α ∨ 2 * (m : ℝ) + 1 < s := by
  let w : ℝ → ℝ := fun x => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)
  let F : ℝ → ℝ := fun x => Real.exp (2 * b * x - 2 * α * |x|) * w x
  have hwpos (x : ℝ) : 0 ≤ w x := by
    dsimp [w]
    apply div_nonneg
    · rw [pow_mul]; positivity
    · positivity
  have hFpos (x : ℝ) : 0 ≤ F x := mul_nonneg (Real.exp_pos _).le (hwpos x)
  have hFc : Continuous F := (by fun_prop : Continuous (fun x : ℝ =>
    Real.exp (2 * b * x - 2 * α * |x|))).mul (weight_cont m s)
  have hbx (x : ℝ) : b * x ≤ |b| * |x| := by
    simpa only [abs_mul] using le_abs_self (b * x)
  change Integrable F ↔ _
  constructor
  · intro hi
    by_cases hstrict : |b| < α
    · exact Or.inl hstrict
    · right
      have heq : |b| = α := le_antisymm hb (le_of_not_gt hstrict)
      have hside : IntegrableOn w (Ioi 0) := by
        by_cases hb0 : 0 ≤ b
        · have hba : b = α := by simpa [abs_of_nonneg hb0] using heq
          apply hi.integrableOn.congr_fun _ measurableSet_Ioi
          intro x hx
          dsimp [F]
          rw [abs_of_pos hx, hba]
          simp
        · have hba : -b = α := by simpa [abs_of_neg (lt_of_not_ge hb0)] using heq
          have href : Integrable (fun x => F (-x)) := hi.comp_neg
          apply href.integrableOn.congr_fun _ measurableSet_Ioi
          intro x hx
          dsimp [F, w]
          rw [abs_neg, abs_of_pos hx, ← hba]
          simp [pow_mul]
      have hw : Integrable w := integrable_even_of_pos w
        (by intro x; simp [w, pow_mul]) hside
      exact (MasulloGRH.sobolev_jet_weight_integrable_iff m s hs).mp hw
  · intro h
    rcases h with hstrict | horder
    · let c : ℝ := 2 * (α - |b|)
      have hc : 0 < c := by dsimp [c]; linarith
      apply (integrable_exp_abs_pow m c hc).mono' hFc.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hFpos x)]
      have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-c * |x|) := by
        apply Real.exp_le_exp.mpr
        dsimp [c]
        nlinarith [hbx x]
      have hden : 1 ≤ (1 + x ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
      have hwle : w x ≤ x ^ (2 * m) := by
        dsimp [w]
        exact div_le_self (by rw [pow_mul]; positivity) hden
      exact mul_le_mul hexp hwle (hwpos x) (Real.exp_pos _).le
    · have hw : Integrable w := (MasulloGRH.sobolev_jet_weight_integrable_iff m s hs).mpr horder
      apply hw.mono' hFc.aestronglyMeasurable
      apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (hFpos x)]
      have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
        nlinarith [hbx x]
      exact mul_le_of_le_one_left (hwpos x) hexp
