-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.measure_unitDyadicGridBadIncrement_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:11:47.498338+00:00
-- url     : https://prove2.me/submissions/52c6cc62-ee28-4199-9b1d-c4dad0390f24

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Process.Kolmogorov
import Definitions.Def_MarkovProcess_FiniteGridFoundations
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_measure_finiteGridBadIncrement_le
import Theorems.Thm_MarkovProcess_unitDyadicGrid_edist_adjacent_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

theorem solution
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (n : ℕ) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P (finiteGridBadIncrement X (unitDyadicGrid n) p ε) ≤
      2 ^ n * (M * (((2 : ℝ≥0∞) ^ n)⁻¹) ^ q / ε ^ p) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    IsKolmogorovProcess.measure_finiteGridBadIncrement_le hX (unitDyadicGrid n) _ ε
      (unitDyadicGrid_edist_adjacent_le n) hε0 hεtop
