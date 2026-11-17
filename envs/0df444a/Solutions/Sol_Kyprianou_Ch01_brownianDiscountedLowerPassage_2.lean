-- Prove2me | solution 2 for Kyprianou.Ch01.brownianDiscountedLowerPassage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:13:21.24667+00:00
-- url     : https://prove2.me/submissions/f9f1e744-7582-424d-84fb-c3509300baf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_brownianDiscountedUpperPassage
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierImmediate
import Theorems.Thm_Kyprianou_Ch01_isLinearBrownian_neg
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_eq_firstUpperPassage_neg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reflection reduces the negative-barrier formula to upper passage, with a true zero case. -/
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
  · have hz := brownianLowerZeroBarrierImmediate
      P X sigma gamma q hsigma hq hX hMeas
    have heq : a = 0 := hzero.symm
    subst a
    simpa using hz
  · have hn := isLinearBrownian_neg P X sigma gamma hX
    have hMeasNeg (t : ℝ≥0) : Measurable (fun ω => -X t ω) := (hMeas t).neg
    have hu := brownianDiscountedUpperPassage P
      (fun t ω => -X t ω) sigma (-gamma) q a
      hsigma hq hpos hn hMeasNeg
    have hpath := firstLowerPassage_eq_firstUpperPassage_neg X a
    simpa only [← hpath, neg_sq, sub_neg_eq_add] using hu
