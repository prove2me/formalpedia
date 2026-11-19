-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperZeroBarrierLaplaceIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:25:54.860503+00:00
-- url     : https://prove2.me/submissions/3a21f650-9ab4-4645-b84b-a4e72530bf8d

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_rationalStrictUpperPassageInfEqualContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceMeasurableFromTimePublic
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Zero-barrier payoff is integrable by a.s. rational-passage measurability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (passageLaplace (firstUpperPassage X 0) q) P := by
  let ratT : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ r : ℚ,
      if (0 < (r : ℝ) ∧ (0 : ℝ) < X (Real.toNNReal (r : ℝ)) ω)
        then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
        else ⊤
  have hRat : Measurable ratT :=
    rationalStrictUpperPassageInfMeasurablePublic X 0 hMeas
  have hLap : Measurable (passageLaplace ratT q) :=
    passageLaplaceMeasurableFromTimePublic ratT q hRat
  have heq : ∀ᵐ ω ∂P, passageLaplace (firstUpperPassage X 0) q ω =
      passageLaplace ratT q ω := by
    filter_upwards [hX.2.1] with ω hc
    have hp := rationalStrictUpperPassageInfEqualContinuousPublic X ω 0 hc
    change firstUpperPassage X 0 ω = ratT ω at hp
    simp only [passageLaplace, hp]
  have hEqSymm : passageLaplace ratT q =ᵐ[P]
      passageLaplace (firstUpperPassage X 0) q := by
    filter_upwards [heq] with ω hw
    exact hw.symm
  have hmeas : AEStronglyMeasurable
      (passageLaplace (firstUpperPassage X 0) q) P :=
    hLap.aestronglyMeasurable.congr hEqSymm
  apply Integrable.of_bound hmeas 1
  exact Filter.Eventually.of_forall (fun ω =>
    passageLaplaceNormBoundNonnegativeDiscountPublic
      (firstUpperPassage X 0) q (le_of_lt hq) ω)
