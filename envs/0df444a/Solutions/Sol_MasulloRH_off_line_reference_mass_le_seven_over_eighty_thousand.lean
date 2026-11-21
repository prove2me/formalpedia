-- Prove2me | solution 1 for MasulloRH.off_line_reference_mass_le_seven_over_eighty_thousand
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:21:40.253173+00:00
-- url     : https://prove2.me/submissions/4b2af9a4-df25-40cc-b4fb-cc4ad355d14e

-- Unconditional spectral estimate for the rational theta cutoff frontier.
import Theorems.Thm_MasulloRH_reference_real_resolvent_sandwich
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_certified_height_99998_reference_budget
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH

theorem solution :
    (∑' z : {z : ZetaZerosInTraceStrip (1/2) // z.val.re ≠ 1/2},
      (zeroResolventTerm (1/2) 3 z.val).re) ≤ 7/80000 := by
  classical
  let Z := ZetaZerosInTraceStrip (1/2)
  let n : ℕ := 49998
  let H : ℝ := 5/2+2*n
  let A : Set Z := {z | z.val.re ≠ 1/2}
  let B : Set Z := {z | H < |z.val.im|}
  let k := fun z : Z => (zeroResolventTerm (1/2) 3 z).re
  let w := zeroDecayWeight (1/2)
  obtain ⟨hcov,hbudget⟩ := certified_height_99998_reference_budget
  have hab : A ⊆ B := by
    intro z hz
    exact lt_of_not_ge (fun h => hz (hcov z h))
  have hw : Summable w := weighted_zero_summability (1/2) (by norm_num)
  have hk : Summable k := by
    apply hw.of_norm_bounded
    intro z
    have h := reference_real_resolvent_sandwich z
    have hnn : 0 ≤ w z := by dsimp [w,zeroDecayWeight]; positivity
    rw [Real.norm_eq_abs,abs_le]
    change -w z ≤ (zeroResolventTerm (1/2) 3 z).re ∧ _ ≤ w z
    change w z/4 ≤ _ ∧ _ ≤ w z/2 at h
    constructor <;> linarith only [h.1,h.2,hnn]
  have hpt (z : Z) : 2*A.indicator k z ≤ B.indicator w z := by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem (hab hz)]
      have h := (reference_real_resolvent_sandwich z).2
      change _ ≤ w z/2 at h
      dsimp only [k]; linarith only [h]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      by_cases h : z ∈ B
      · rw [Set.indicator_of_mem h]; dsimp [w,zeroDecayWeight]; positivity
      · simp [Set.indicator_of_notMem h]
  have hs := ((hk.indicator A).mul_left (2:ℝ)).tsum_le_tsum hpt (hw.indicator B)
  rw [tsum_mul_left] at hs
  have herr : (∑' z,B.indicator w z) ≤ (7/40000:ℝ) := by
    change (∑' z : Z, if H < |z.val.im| then w z else 0) ≤ _
    apply (zero_decay_tail_at_real_lattice n).trans
    exact hbudget.trans (by norm_num)
  change (∑' z : A,k z) ≤ _
  rw [tsum_subtype A k]
  linarith only [hs,herr]
