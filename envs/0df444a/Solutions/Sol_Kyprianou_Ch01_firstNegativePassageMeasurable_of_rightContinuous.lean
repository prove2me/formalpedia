-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageMeasurable_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T19:20:21.032859+00:00
-- url     : https://prove2.me/submissions/ff0731be-93fd-4b45-ac64-8972642c7a8c

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_rationalFirstNegativePassageMeasurable
import Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rational_of_rightContinuous
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Sections + pathwise right-continuity ⇒ Borel measurability of `firstNegativePassage`. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t))
    (hright : ∀ ω : Ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  let C : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ r : ℚ,
      if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤
  have hCm : Measurable C :=
    Kyprianou.Ch01.rationalFirstNegativePassageMeasurable X hX
  have hEq : (fun ω => firstNegativePassage X ω) = C :=
    funext fun ω =>
      Kyprianou.Ch01.firstNegativePassage_eq_rational_of_rightContinuous X ω (hright ω)
  simpa [hEq] using hCm
