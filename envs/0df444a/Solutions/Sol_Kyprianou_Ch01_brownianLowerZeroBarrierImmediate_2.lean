-- Prove2me | solution 2 for Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:31:28.062092+00:00
-- url     : https://prove2.me/submissions/a4a8c3ac-f352-4ded-ae87-2bc31c1885e6

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_brownianUpperZeroBarrierLaplaceOne
import Theorems.Thm_Kyprianou_Ch01_isLinearBrownian_neg
import Theorems.Thm_Kyprianou_Ch01_firstLowerPassage_eq_firstUpperPassage_neg
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
    (sigma gamma q : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q) P ∧
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q ω ∂P) = 1 := by
  have hneg : IsLinearBrownian P
      (fun t ω => -X t ω) sigma (-gamma) :=
    isLinearBrownian_neg P X sigma gamma hX
  have hmeasNeg : ∀ t : ℝ≥0,
      Measurable (fun ω => -X t ω) :=
    fun t => (hMeas t).neg
  have hup := brownianUpperZeroBarrierLaplaceOne P
    (fun t ω => -X t ω) sigma (-gamma) q
      hsigma hq hneg hmeasNeg
  have hpass :
      firstLowerPassage X 0 0 =
        firstUpperPassage (fun t ω => -X t ω) 0 := by
    simpa only [neg_zero] using
      firstLowerPassage_eq_firstUpperPassage_neg X 0
  rw [hpass]
  exact hup
