-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperPassageLaplaceAEStrongMeasurablePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:37:29.682137+00:00
-- url     : https://prove2.me/submissions/0127565a-dd35-4ca1-8dc9-1e7bcdac9000

import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfEqualContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceMeasurableFromTimePublic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- On a.s. continuous paths, the rational first passage equals the original passage. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    AEStronglyMeasurable (passageLaplace (firstUpperPassage X x) q) P := by
  let ratT : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ r : ℚ,
      if (0 < (r : ℝ) ∧ x < X (Real.toNNReal (r : ℝ)) ω)
        then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
        else ⊤
  have hRat : Measurable ratT :=
    rationalStrictUpperPassageInfMeasurablePublic X x hMeas
  have hLap : Measurable (passageLaplace ratT q) :=
    passageLaplaceMeasurableFromTimePublic ratT q hRat
  have heq : ∀ᵐ ω ∂P, passageLaplace (firstUpperPassage X x) q ω =
      passageLaplace ratT q ω := by
    filter_upwards [hX.2.1] with ω hc
    have hp := rationalStrictUpperPassageInfEqualContinuousPublic X ω x hc
    change (match firstUpperPassage X x ω with
      | none => (0 : ℝ)
      | some t => Real.exp (-q * (t : ℝ))) =
      (match ratT ω with
      | none => (0 : ℝ)
      | some t => Real.exp (-q * (t : ℝ)))
    change firstUpperPassage X x ω = ratT ω at hp
    rw [hp]
  have hEqSymm : passageLaplace ratT q =ᵐ[P]
      passageLaplace (firstUpperPassage X x) q := by
    filter_upwards [heq] with ω hw
    exact hw.symm
  exact hLap.aestronglyMeasurable.congr hEqSymm
