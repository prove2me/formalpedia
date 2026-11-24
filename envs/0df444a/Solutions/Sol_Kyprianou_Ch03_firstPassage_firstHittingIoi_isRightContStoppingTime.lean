-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassage_firstHittingIoi_isRightContStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:18:33.173115+00:00
-- url     : https://prove2.me/submissions/769c1a2d-d3e6-4d10-b477-7c890713c3bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Upward first-passage time `τ_x^+ = firstHittingTime X (Ioi x)` is an `F₊`-stopping time.

Reduction:
1. Pathwise identify `firstHittingTime` with `twoSidedExitUpTimeCorrected` (Proved).
2. Unfold: `twoSidedExitUpTimeCorrected` agrees with `twoSidedExitUpTime`.
3. Apply `upperPassage_stopping_rightCont_filtration` (the `F₊` form of
   `upperPassage_isStoppingTime_of_rightContinuous`).
-/

namespace Kyprianou.Ch03

private lemma correctedUpTime_eq_upTime
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    twoSidedExitUpTimeCorrected X b ω = twoSidedExitUpTime X b ω :=
  rfl

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) (hx : 0 < x) :
    IsStoppingTime F.rightCont
      (fun omega => firstHittingTime L.X (Set.Ioi x) omega) := by
  have heq :
      (fun omega => firstHittingTime L.X (Set.Ioi x) omega) =
        twoSidedExitUpTime L x := by
    funext omega
    rw [firstHittingIoi_eq_correctedUpTime P F L x hx omega]
    exact correctedUpTime_eq_upTime L x omega
  rw [heq]
  exact upperPassage_stopping_rightCont_filtration L x
