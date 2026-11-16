-- Prove2me | solution 1 for ListReplicableBias.LowerBound.Supplement.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:00:55.561853+00:00
-- url     : https://prove2.me/submissions/ad563f49-02ab-45fa-b699-9fe0075e3e37

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_Geometry
import Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open ListReplicableBias.LowerBound ListReplicableBias.LowerBound.Supplement

lemma lrb64_floor_eq {ε z : ℝ} (k : ℤ) (hε : 0 < ε)
    (hz : z ∈ Set.Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)) : ⌊z / ε⌋ = k := by
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := hz
  constructor
  · rw [le_div_iff₀ hε]; exact h1
  · rw [div_lt_iff₀ hε]; exact h2

theorem solution (ε u α p phat : ℝ) (hu : u ∈ Set.Ico (0 : ℝ) ε) (hα : 0 < α)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hphat : phat ∈ Set.Icc (0 : ℝ) 1)
    (hclose : |phat - p| ≤ α) :
    (IsGoodShift ε α p u →
      ∀ x ∈ Set.Ico (p - α) (p + α), ∀ y ∈ Set.Ico (p - α) (p + α),
        roundShift ε u x = roundShift ε u y) ∧
    (IsGoodShift ε (3 * α) p u → IsGoodShift ε (2 * α) phat u) ∧
    (IsGoodShift ε (2 * α) phat u → roundShift ε u p = roundShift ε u phat) := by
  have hε : 0 < ε := lt_of_le_of_lt hu.1 hu.2
  have hc := abs_le.mp hclose
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩ x hx y hy
    have hx' : x + u ∈ Set.Ico ((p + u) - α) ((p + u) + α) :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : y + u ∈ Set.Ico ((p + u) - α) ((p + u) + α) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    unfold roundShift
    rw [lrb64_floor_eq k hε (hk hx'), lrb64_floor_eq k hε (hk hy')]
  · rintro ⟨k, hk⟩
    refine ⟨k, fun z hz => hk ⟨?_, ?_⟩⟩
    · linarith [hz.1]
    · linarith [hz.2]
  · rintro ⟨k, hk⟩
    have hx' : p + u ∈ Set.Ico ((phat + u) - 2 * α) ((phat + u) + 2 * α) :=
      ⟨by linarith, by linarith⟩
    have hy' : phat + u ∈ Set.Ico ((phat + u) - 2 * α) ((phat + u) + 2 * α) :=
      ⟨by linarith, by linarith⟩
    unfold roundShift
    rw [lrb64_floor_eq k hε (hk hx'), lrb64_floor_eq k hε (hk hy')]
