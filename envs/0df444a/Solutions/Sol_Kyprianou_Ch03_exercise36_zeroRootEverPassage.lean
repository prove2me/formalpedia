-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_zeroRootEverPassage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:37:50.310209+00:00
-- url     : https://prove2.me/submissions/e11ca279-7922-4753-a08b-f4ccf4aadeeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
import Theorems.Thm_Kyprianou_Ch03_hitFinite_iff_everExceeds
import Theorems.Thm_Kyprianou_Ch03_firstHittingFinite_timeSelector
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
{Omega OmegaE : Type}
    [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q)
    (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal =
        Real.exp (-q * (t : ℝ))) :
    (∃ phi0 : ℝ, 0 ≤ phi0 ∧ L.ψ phi0 = 0 ∧
        (∀ theta : ℝ, 0 ≤ theta →
          L.ψ theta = 0 → theta ≤ phi0) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {omega : Omega |
            ∃ t : NNReal, x < L.X t omega}).toReal =
          Real.exp (-phi0 * x)) := by
  rcases Kyprianou.Ch03.firstPassageZero_maximalRootExistence
      P F L hNotDecreasing with ⟨phi0, hpos, hzero, hmax⟩
  refine ⟨phi0, hpos, hzero, hmax, ?_⟩
  refine fun x hx => ?_
  obtain ⟨f, hf⟩ :=
    Kyprianou.Ch03.firstHittingFinite_timeSelector L.X (Set.Ioi x)
  have htail :=
    Kyprianou.Ch03.firstPassageZero_consequence1
      P F L hNotDecreasing phi0 ⟨hpos, hzero, hmax⟩
      x hx f hf
  have hSet :
      {omega : Omega | ∃ t : NNReal, x < L.X t omega} =
      {omega : Omega |
        firstHittingTime L.X (Set.Ioi x) omega != ⊤} := by
    ext omega
    exact Kyprianou.Ch03.hitFinite_iff_everExceeds P F L x hx omega
  rw [hSet]
  exact htail

