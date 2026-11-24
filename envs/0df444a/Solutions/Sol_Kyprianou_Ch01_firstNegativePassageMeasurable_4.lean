-- Prove2me | solution 4 for Kyprianou.Ch01.firstNegativePassageMeasurable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:32:43.79799+00:00
-- url     : https://prove2.me/submissions/2d01c0e0-6967-48a5-8b04-2fc71fcd9260
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_rightContinuous_of_joint
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable_of_rightContinuous
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Sketch: joint ⇒ RC (open child) + Proved `of_rightContinuous`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  have hsec : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
    hX.comp (measurable_id.prodMk measurable_const)
  have hrc := Kyprianou.Ch01.rightContinuous_of_joint X hX
  exact Kyprianou.Ch01.firstNegativePassageMeasurable_of_rightContinuous X hsec hrc
