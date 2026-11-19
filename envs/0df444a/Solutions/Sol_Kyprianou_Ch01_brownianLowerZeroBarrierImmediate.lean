-- Prove2me | solution 1 for Kyprianou.Ch01.brownianLowerZeroBarrierImmediate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:05:43.855017+00:00
-- url     : https://prove2.me/submissions/876b469a-75bd-470c-9e33-ec8c120d520b

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_brownianLowerZeroBarrierPassageAeZero
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
  have hτ := Kyprianou.Ch01.brownianLowerZeroBarrierPassageAeZero
    P X sigma gamma hsigma hX hMeas
  have hp :
      (fun ω => Kyprianou.Ch01.passageLaplace
        (Kyprianou.Ch01.firstLowerPassage X 0 0) q ω) =ᵐ[P]
          (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [hτ] with ω hω
    simp [Kyprianou.Ch01.passageLaplace, hω]
  have hint : Integrable (Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q) P :=
    (integrable_const (1 : ℝ)).congr hp.symm
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, Kyprianou.Ch01.passageLaplace
      (Kyprianou.Ch01.firstLowerPassage X 0 0) q ω ∂P) =
        ∫ _ω : Ω, (1 : ℝ) ∂P := integral_congr_ae hp
    _ = 1 := by simp
