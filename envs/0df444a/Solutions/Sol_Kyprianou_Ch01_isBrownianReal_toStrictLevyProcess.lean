-- Prove2me | solution 1 for Kyprianou.Ch01.isBrownianReal_toStrictLevyProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:04.143383+00:00
-- url     : https://prove2.me/submissions/5b4c1fec-9606-4591-8367-b4e6b8f52ecc

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_isPreBrownianReal_initial_zero_ae
import Theorems.Thm_Kyprianou_Ch01_brownianInitialValueNormalization
import Theorems.Thm_Kyprianou_Ch01_isLevyProcess_of_isPreBrownianReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal X P) :
    IsLevyProcess (fun t ω => X t ω - X 0 ω) P := by
  let Z : ℝ≥0 → Ω → ℝ := fun t ω => X t ω - X 0 ω
  have hzero : ∀ᵐ ω ∂P, X 0 ω = 0 :=
    Kyprianou.Ch01.isPreBrownianReal_initial_zero_ae
      P X hB.toIsPreBrownianReal
  have hp : IsPreBrownianReal Z P :=
    Kyprianou.Ch01.brownianInitialValueNormalization
      P X hB.toIsPreBrownianReal hzero
  have hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => Z t ω) := by
    filter_upwards [hB.cont] with omega hc
    exact hc.sub continuous_const
  have hstart : Z 0 = fun _ => 0 := by
    funext omega
    simp [Z]
  exact Kyprianou.Ch01.isLevyProcess_of_isPreBrownianReal P Z hp hstart hcont
