-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstArrivalNotAntitoneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:13:19.715141+00:00
-- url     : https://prove2.me/submissions/9f2d50f0-a8a6-4a8c-b1c1-318d1d847025

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal)
    (hPos : ∀ᵐ w ∂P, 0 < a w)
    (hPrefix : ∀ᵐ w ∂P, ∀ s : NNReal, s < a w → L.X s w = (s : Real)) :
    ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)) := by
  intro h
  have hf : ∀ᵐ w ∂P, False := by
    filter_upwards [hPos, hPrefix, h] with w hp hpre hm
    have hs : 0 < a w / 2 := by positivity
    have hlt : a w / 2 < a w := by
      exact div_lt_self hp (by norm_num)
    have hh := hm (show (0 : NNReal) ≤ a w / 2 from zero_le)
    change L.X (a w / 2) w ≤ L.X 0 w at hh
    rw [hpre _ hlt, L.X_zero] at hh
    exact (not_le_of_gt (show (0 : Real) < ((a w / 2 : NNReal) : Real) from by
      exact_mod_cast hs)) hh
  have hz : P = 0 := by simpa using hf
  have hu : P Set.univ = 1 := measure_univ
  rw [hz] at hu
  simp at hu
