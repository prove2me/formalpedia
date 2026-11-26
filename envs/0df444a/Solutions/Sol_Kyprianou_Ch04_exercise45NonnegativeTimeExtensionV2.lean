-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:26:58.971977+00:00
-- url     : https://prove2.me/submissions/8fd024af-2347-4ef6-bb86-b386a3467de6

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (fun z : ℝ × ℝ => f (max z.1 0) z.2) := by
  exact hf.comp_continuous
    ((continuous_fst.max continuous_const).prodMk continuous_snd)
    (fun z => ⟨show (0 : ℝ) ≤ max z.1 0 from le_max_right _ _,Set.mem_univ _⟩)
