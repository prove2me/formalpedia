-- Prove2me | solution 1 for Kyprianou.Ch01.inverseReciprocalOccupationRationalInf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:24:00.879691+00:00
-- url     : https://prove2.me/submissions/8087b3b1-e6bd-4cca-82ba-9971c6c9a24d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
import Theorems.Thm_Kyprianou_Ch01_inverseReciprocalOccupationRationalCrossingBefore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Countable rational upper-crossing representation of the strict inverse clock. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (t : ℝ≥0) :
    inverseReciprocalOccupation X t ω =
      ⨅ q : ℚ,
        if (0 < (q : ℝ) ∧
            (t : ℝ≥0∞) <
              reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω)
          then ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0)
          else ⊤  := by
  classical
  let F (q : ℚ) : WithTop ℝ≥0 :=
    if (0 < (q : ℝ) ∧
        (t : ℝ≥0∞) <
          reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω)
      then ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0)
      else ⊤
  change inverseReciprocalOccupation X t ω = ⨅ q, F q
  have hRatLe (q : ℚ) (hqpos : 0 < (q : ℝ))
      (hqval : (t : ℝ≥0∞) <
        reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω) :
      (⨅ r, F r) ≤ ((Real.toNNReal (q : ℝ)) : WithTop ℝ≥0) := by
    have hqRat : (0 : ℚ) < q := by exact_mod_cast hqpos
    simpa [F, hqRat, hqval] using (iInf_le (fun r => F r) q)
  apply le_antisymm
  · apply le_iInf
    intro q
    change inverseReciprocalOccupation X t ω ≤ F q
    by_cases hq : 0 < (q : ℝ) ∧
        (t : ℝ≥0∞) < reciprocalOccupation X (Real.toNNReal (q : ℝ)) ω
    · simp only [F, if_pos hq]
      have hex : ∃ s : ℝ≥0,
          (t : ℝ≥0∞) < reciprocalOccupation X s ω :=
        ⟨Real.toNNReal (q : ℝ), hq.2⟩
      have hle : sInf {s : ℝ≥0 |
          (t : ℝ≥0∞) < reciprocalOccupation X s ω} ≤
            Real.toNNReal (q : ℝ) :=
        csInf_le (OrderBot.bddBelow _) hq.2
      simpa [inverseReciprocalOccupation, hex] using
        (WithTop.coe_le_coe.mpr hle)
    · simp only [F, if_neg hq]
      exact le_top
  · refine le_of_forall_gt (fun (upper : WithTop ℝ≥0) hUpper => ?_)
    cases upper with
    | top =>
        cases hInv : inverseReciprocalOccupation X t ω with
        | top =>
            simp [hInv] at hUpper
        | coe s =>
            have hLater : inverseReciprocalOccupation X t ω <
                ((s + 1 : ℝ≥0) : WithTop ℝ≥0) := by
              rw [hInv]
              exact WithTop.coe_lt_coe.mpr
                (lt_add_of_pos_right s one_pos)
            obtain ⟨q, hqpos, hqbound, hqval⟩ :=
              Kyprianou.Ch01.inverseReciprocalOccupationRationalCrossingBefore
                X ω t (s + 1) hLater
            exact lt_of_le_of_lt (hRatLe q hqpos hqval)
              (WithTop.coe_lt_top _)
    | coe upperTime =>
        obtain ⟨q, hqpos, hqbound, hqval⟩ :=
          Kyprianou.Ch01.inverseReciprocalOccupationRationalCrossingBefore
            X ω t upperTime hUpper
        exact lt_of_le_of_lt (hRatLe q hqpos hqval)
          (WithTop.coe_lt_coe.mpr hqbound)
