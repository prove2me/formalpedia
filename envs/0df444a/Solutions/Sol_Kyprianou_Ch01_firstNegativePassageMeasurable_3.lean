-- Prove2me | solution 3 for Kyprianou.Ch01.firstNegativePassageMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T18:04:40.382843+00:00
-- url     : https://prove2.me/submissions/10cbabc1-3a94-48aa-9f04-40a4ef5f1afd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_measurable_eval_of_joint
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable_of_sections
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-!
Corrected sketch: the rational-identification leaf is false without path
regularity (spike at an irrational time). Reduce instead to measurable
sections, then to measurability of `firstNegativePassage` from sections.
-/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  exact Kyprianou.Ch01.firstNegativePassageMeasurable_of_sections X
    (Kyprianou.Ch01.measurable_eval_of_joint X hX)
