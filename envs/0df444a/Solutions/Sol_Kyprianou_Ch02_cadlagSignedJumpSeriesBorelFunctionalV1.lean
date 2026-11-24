-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagSignedJumpSeriesBorelFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:49.174808+00:00
-- url     : https://prove2.me/submissions/1029f470-9d2f-4ccf-817e-8041605a3fd9

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_cadlagWeightedJumpSumBorelFunctionalV1
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Recover the signed jump sum from two nonnegative measurable sums. -/
theorem solution
    (T : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ t : ℝ≥0, ContinuousWithinAt Y (Set.Ici t) t) →
        (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto Y (𝓝[<] t) (𝓝 l)) →
        Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
          |Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)|) →
        F Y = ∑' s : Set.Ioc (0 : ℝ≥0) T,
          (Y (s : ℝ≥0) - Function.leftLim Y (s : ℝ≥0)) := by
  let p : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (max x 0)
  let q : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (-x) 0)
  have hp : Measurable p := ENNReal.measurable_ofReal.comp
    (measurable_id.max measurable_const)
  have hq : Measurable q := ENNReal.measurable_ofReal.comp
    (measurable_id.neg.max measurable_const)
  obtain ⟨F, hF, hFp⟩ :=
    Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1 T p hp (by simp [p])
  obtain ⟨G, hG, hGq⟩ :=
    Kyprianou.Ch02.cadlagWeightedJumpSumBorelFunctionalV1 T q hq (by simp [q])
  refine ⟨fun Y => (F Y).toReal - (G Y).toReal,
    (ENNReal.measurable_toReal.comp hF).sub
      (ENNReal.measurable_toReal.comp hG), ?_⟩
  intro Y hR hL hs
  let j : Ioc (0 : ℝ≥0) T → ℝ := fun s => Y s - Function.leftLim Y s
  have hpos : Summable (fun s => max (j s) 0) :=
    hs.of_nonneg_of_le (fun s => le_max_right _ _) (fun s => by
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hneg : Summable (fun s => max (-j s) 0) :=
    hs.of_nonneg_of_le (fun s => le_max_right _ _) (fun s => by
      exact max_le (neg_le_abs _) (abs_nonneg _))
  change (F Y).toReal - (G Y).toReal = ∑' s, j s
  rw [hFp Y hR hL, hGq Y hR hL]
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp only [p, q, ENNReal.toReal_ofReal (le_max_right _ _)]
  change (∑' s, max (j s) 0) - (∑' s, max (-j s) 0) = ∑' s, j s
  rw [← hpos.tsum_sub hneg]
  apply tsum_congr
  intro s
  rcases le_total 0 (j s) with h | h
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
