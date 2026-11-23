-- Prove2me | solution 1 for Kyprianou.Ch02.prmUnitStripsFiniteMassAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:15:26.663797+00:00
-- url     : https://prove2.me/submissions/e95c4f36-2578-4626-9258-208b3024c1fd

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finitePoissonTimeMarkCellIntensity
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ico (n : ℝ) (n + 1) ×ˢ B) = k := by
  rw [ae_all_iff]
  intro n
  have hfin : LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ico (n : ℝ) (n + 1) ×ˢ B) ≠ ⊤ :=
    Kyprianou.Ch02.finitePoissonTimeMarkCellIntensity
      ν (fun _ => B) (fun _ => hB) (fun _ => hfinite) (n, 0)
  exact N.integer_valued (measurableSet_Ico.prod hB) hfin

