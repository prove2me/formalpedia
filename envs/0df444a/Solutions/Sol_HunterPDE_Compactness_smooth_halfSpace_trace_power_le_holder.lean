-- Prove2me | solution 1 for HunterPDE.Compactness.smooth_halfSpace_trace_power_le_holder
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:45:58.144777+00:00
-- url     : https://prove2.me/submissions/a90ff5d3-5af5-45ac-86bd-1bd6cb2be33e

import Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_lintegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsSmoothCompactClosedHalfSpace f) :
    eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) 0 f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) ^ ((p.toReal - 1) / p.toReal) *
        (eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m)
            (Pi.single (Fin.last m) 1) f)
            p (volume.restrict (upperHalfSpace m)) ^ p.toReal) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hr1 : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_mono hp' hp)
  have hr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hr1
  have hmeas (α : Fin (m + 1) → ℕ) :
      AEMeasurable (fun x => ‖HunterPDE.Shared.weakDeriv (upperHalfSpace m) α f x‖ₑ)
        (volume.restrict (upperHalfSpace m)) := by
    unfold HunterPDE.Shared.weakDeriv
    split_ifs with h
    · exact h.choose_spec.2.1.aestronglyMeasurable.enorm
    · simpa only [Pi.zero_apply, enorm_zero] using
        (aemeasurable_const : AEMeasurable
          (fun _ : EuclideanSpace ℝ (Fin (m + 1)) => (0 : ℝ≥0∞))
          (volume.restrict (upperHalfSpace m)))
  have he (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) :
      (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume.restrict (upperHalfSpace m)) =
        eLpNorm g p (volume.restrict (upperHalfSpace m)) ^ p.toReal := by
    rw [eLpNorm_eq_eLpNorm' hp0 hp']
    exact lintegral_rpow_enorm_eq_rpow_eLpNorm' hr0
  have ha : 0 ≤ (p.toReal - 1) / p.toReal := div_nonneg (sub_nonneg.mpr hr1) hr0.le
  have hb : 0 ≤ 1 / p.toReal := div_nonneg zero_le_one hr0.le
  have hab : (p.toReal - 1) / p.toReal + 1 / p.toReal = 1 := by
    rw [← add_div, sub_add_cancel, div_self hr0.ne']
  have hmul1 : p.toReal * ((p.toReal - 1) / p.toReal) = p.toReal - 1 := by
    field_simp [hr0.ne']
  have hmul2 : p.toReal * (1 / p.toReal) = 1 := by
    field_simp [hr0.ne']
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    ((hmeas 0).pow_const p.toReal)
    ((hmeas (Pi.single (Fin.last m) 1)).pow_const p.toReal) ha hb hab
  simp only [← ENNReal.rpow_mul, hmul1, hmul2, ENNReal.rpow_one] at hholder
  rw [he, he] at hholder
  exact (HunterPDE.Compactness.smooth_halfSpace_trace_power_le_lintegral p hp hp' f hf).trans
    ((mul_le_mul_right hholder (ENNReal.ofReal p.toReal)).trans_eq (mul_assoc _ _ _).symm)
