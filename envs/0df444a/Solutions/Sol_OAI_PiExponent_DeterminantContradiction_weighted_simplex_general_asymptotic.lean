-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_general_asymptotic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T02:36:28.167512+00:00
-- url     : https://prove2.me/submissions/f828498c-8f24-4f70-8454-786d0941fb6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_bounds

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    (m : ℕ) (w : Fin m → ℝ) (A : ℝ)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto
      (fun H : ℝ => ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : ℝ) / H ^ m)
      atTop
      (𝓝 (A ^ m /
        ((Nat.factorial m : ℝ) * ∏ i : Fin m, w i))) := by
  let D : ℝ := (Nat.factorial m : ℝ) * ∏ i : Fin m, w i
  let S : ℝ := ∑ i : Fin m, w i
  have hsmall : Tendsto (fun H : ℝ => S / H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hupper : Tendsto (fun H : ℝ => (A + S / H) ^ m / D)
      atTop (𝓝 (A ^ m / D)) := by
    simpa only [add_zero] using
      (((tendsto_const_nhds (x := A)).add hsmall).pow m).div_const D
  have hb : ∀ᶠ H : ℝ in atTop,
      A ^ m / D ≤ ((realWeightedSimplex w (A * H)).card : ℝ) / H ^ m ∧
      ((realWeightedSimplex w (A * H)).card : ℝ) / H ^ m ≤
        (A + S / H) ^ m / D := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    have h := weighted_simplex_volume_bounds m w (A * H) hw
      (mul_nonneg hA.le hH.le)
    change (A * H) ^ m / D ≤ ((realWeightedSimplex w (A * H)).card : ℝ) ∧
      ((realWeightedSimplex w (A * H)).card : ℝ) ≤ (A * H + S) ^ m / D at h
    have hpow : 0 < H ^ m := pow_pos hH m
    have hlo := div_le_div_of_nonneg_right h.1 hpow.le
    have hhi := div_le_div_of_nonneg_right h.2 hpow.le
    have hscale : (A * H) ^ m / D / H ^ m = A ^ m / D := by
      rw [div_right_comm, mul_pow, mul_div_cancel_right₀ _ (ne_of_gt hpow)]
    have hshift : (A * H + S) ^ m / D / H ^ m = (A + S / H) ^ m / D := by
      rw [div_right_comm, ← div_pow, add_div,
        mul_div_cancel_right₀ _ (ne_of_gt hH)]
    rw [hscale] at hlo
    rw [hshift] at hhi
    exact ⟨hlo, hhi⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
