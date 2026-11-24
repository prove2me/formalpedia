-- Prove2me | solution 2 for Kyprianou.Ch01.firstNegativePassageMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T16:59:01.253298+00:00
-- url     : https://prove2.me/submissions/e1b2245a-4911-435f-96ff-7f7de6d55548
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_measurable_eval_of_joint
import Theorems.Thm_Kyprianou_Ch01_rationalFirstNegativePassageMeasurable
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rational
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-!
Sketch for `Kyprianou.Ch01.firstNegativePassageMeasurable`.

Mirrors the proved firstNonpositiveLattice route
(`rationalFirstNonpositiveLatticeClockMeasurable` →
`firstNonpositiveLatticeEqRationalOfRightContinuous`).
-/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  have hsec := Kyprianou.Ch01.measurable_eval_of_joint X hX
  have hrat :=
    Kyprianou.Ch01.rationalFirstNegativePassageMeasurable X hsec
  have heq :
      (fun ω => firstNegativePassage X ω) =
        fun ω =>
          ⨅ r : ℚ,
            if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
              ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
            else ⊤ := by
    funext ω
    exact Kyprianou.Ch01.firstNegativePassage_eq_rational X hX ω
  simpa [heq] using hrat
