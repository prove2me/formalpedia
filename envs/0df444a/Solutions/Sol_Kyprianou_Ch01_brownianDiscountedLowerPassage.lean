-- Prove2me | solution 1 for Kyprianou.Ch01.brownianDiscountedLowerPassage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:39:11.323261+00:00
-- url     : https://prove2.me/submissions/be125786-066f-412b-8e08-8855efdaaa6d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_isLinearBrownian_neg
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierImmediate
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_eq_firstUpperPassage_neg
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reduce lower Brownian discounting to the upper-barrier transform by
    reflection, with the genuine instantaneous zero-barrier case separate. -/
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
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    have hbase := Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
      P X sigma gamma q hsigma hq hX hMeas
    simpa using hbase
  · have hneg := Kyprianou.Ch01.isLinearBrownian_neg
      P X sigma gamma hX
    have hupper := Kyprianou.Ch01.brownianDiscountedUpperPassage
      P (fun t ω => -X t ω) sigma (-gamma) q a
      hsigma hq hpos hneg (fun t => (hMeas t).neg)
    have hstop := Kyprianou.Ch01.firstLowerPassage_eq_firstUpperPassage_neg X a
    have hpay :
        passageLaplace (firstLowerPassage X 0 (-a)) q =
          passageLaplace (firstUpperPassage (fun t ω => -X t ω) a) q :=
      congrArg (fun T : Ω → WithTop ℝ≥0 => passageLaplace T q) hstop
    simpa only [hpay, neg_sq, sub_neg_eq_add] using hupper
