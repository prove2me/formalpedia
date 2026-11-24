-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:55:49.42907+00:00
-- url     : https://prove2.me/submissions/9c777e66-2e4f-4668-9d56-5b15c23382e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumMonotonePointwiseSummableV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumSeriesSummableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Sketch: unrestricted pointwise mono reduces to the summable inequality once
jump-sum series summability over every `Ioc 0 t` is granted.
(Note: the summability child is the nontrivial path-regularity obligation;
Mathlib's real `∑'` is otherwise `0` off the summable locus.)
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) :
    (∑' s : Ioc (0 : ℝ≥0) a,
        max (X s.1 ω -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0) ≤
      ∑' s : Ioc (0 : ℝ≥0) b,
        max (X s.1 ω -
          limUnder (nhdsWithin s.1 (Iio s.1)) (fun u => X u ω)) 0 :=
  Kyprianou.Ch02.bvLevyPositiveJumpSumMonotonePointwiseSummableV1 X ω a b hab
    (Kyprianou.Ch02.bvLevyPositiveJumpSumSeriesSummableV1 X ω a)
    (Kyprianou.Ch02.bvLevyPositiveJumpSumSeriesSummableV1 X ω b)
