-- Prove2me | solution 3 for Kyprianou.Ch01.brownianDiscountedLowerPassage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:52:39.564934+00:00
-- url     : https://prove2.me/submissions/3610677e-a013-4992-a675-85c1bdbe806a

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_isLinearBrownian_neg
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_eq_firstUpperPassage_neg
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierImmediate
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q a : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (ha : 0 ≤ a)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable
      (passageLaplace (firstLowerPassage X 0 (-a)) q) P ∧
    (∫ ω, passageLaplace (firstLowerPassage X 0 (-a)) q ω ∂P) =
      Real.exp (-a * ((Real.sqrt
        (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2)) := by
  by_cases hpos : 0 < a
  · have hneg : IsLinearBrownian P (fun t ω => -X t ω)
        sigma (-gamma) :=
      Kyprianou.Ch01.isLinearBrownian_neg P X sigma gamma hX
    have hmeasNeg : ∀ t : ℝ≥0, Measurable (fun ω => -X t ω) :=
      fun t => (hMeas t).neg
    have hup := Kyprianou.Ch01.brownianDiscountedUpperPassage
      P (fun t ω => -X t ω) sigma (-gamma) q a
      hsigma hq hpos hneg hmeasNeg
    have hpass := Kyprianou.Ch01.firstLowerPassage_eq_firstUpperPassage_neg X a
    change Integrable
      (passageLaplace (fun ω => firstLowerPassage X 0 (-a) ω) q) P ∧
      (∫ ω, passageLaplace
        (fun ω => firstLowerPassage X 0 (-a) ω) q ω ∂P) =
        Real.exp (-a * ((Real.sqrt
          (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) / sigma ^ 2))
    rw [hpass]
    simpa only [neg_sq, sub_neg_eq_add] using hup
  · have ha0 : a = 0 := le_antisymm (le_of_not_gt hpos) ha
    subst a
    simpa using Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
      P X sigma gamma q hsigma hq hX hMeas
