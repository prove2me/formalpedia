-- Prove2me | solution 1 for Kyprianou.Ch01.inverseReciprocalOccupationRationalCrossingBefore
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:19:52.84341+00:00
-- url     : https://prove2.me/submissions/521a0523-bee8-4eb3-9819-b6a0887cdd7e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Rational strict crossings precede every finite horizon beyond the inverse clock. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (t upper : ℝ≥0)
    (hUpper : inverseReciprocalOccupation X t ω <
      (upper : WithTop ℝ≥0)) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧
      Real.toNNReal (q : ℝ) < upper ∧
      (t : ℝ≥0∞) <
        reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω := by
  classical
  have hMono := Kyprianou.Ch01.reciprocalOccupationMonotone X ω
  by_cases hex : ∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X s ω
  · let S : Set ℝ≥0 := {s | (t : ℝ≥0∞) < reciprocalOccupation X s ω}
    have hne : S.Nonempty := by
      obtain ⟨s, hs⟩ := hex
      exact ⟨s, hs⟩
    have hInv :
        inverseReciprocalOccupation X t ω = ((sInf S : ℝ≥0) : WithTop ℝ≥0) := by
      simp [inverseReciprocalOccupation, hex, S]
      rfl
    have hu : sInf S < upper := by
      exact WithTop.coe_lt_coe.mp (by simpa [hInv] using hUpper)
    obtain ⟨s, hs, hsupper⟩ := exists_lt_of_csInf_lt hne hu
    obtain ⟨q, hqnonneg, hqs, hqupper⟩ :=
      (NNReal.lt_iff_exists_rat_btwn s upper).mp hsupper
    have hqpos : 0 < (q : ℝ) := by
      have hqposNN : (0 : ℝ≥0) < Real.toNNReal (q : ℝ) :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hqs
      exact Real.toNNReal_pos.mp hqposNN
    exact ⟨q, hqpos, hqupper, lt_of_lt_of_le hs (hMono hqs.le)⟩
  · have hInv : inverseReciprocalOccupation X t ω = ⊤ := by
      simp [inverseReciprocalOccupation, hex]
    rw [hInv] at hUpper
    exact False.elim (not_top_lt hUpper)
