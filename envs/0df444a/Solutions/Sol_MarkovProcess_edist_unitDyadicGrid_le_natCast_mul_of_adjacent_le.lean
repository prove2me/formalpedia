-- Prove2me | solution 1 for MarkovProcess.edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:02:59.176354+00:00
-- url     : https://prove2.me/submissions/2357f00a-c68d-4e50-ab1d-5c156106733d

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]


theorem solution
    {X : NNRat → Ω → E} {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    (i j : Fin (2 ^ n + 1)) (hij : (i : ℕ) ≤ j) :
    edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
      (j.val - i.val : ℕ) * ε := by
  let f : ℕ → E := fun k ↦
    if hk : k < 2 ^ n + 1 then X (unitDyadicGrid n ⟨k, hk⟩) ω
    else X (unitDyadicGrid n i) ω
  have hf (k : ℕ) (hk : k < 2 ^ n + 1) :
      f k = X (unitDyadicGrid n ⟨k, hk⟩) ω := by
    simp only [f, dif_pos hk]
  calc
    edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) =
        edist (f i) (f j) := by rw [hf i i.isLt, hf j j.isLt]
    _ ≤ ∑ _k ∈ Finset.Ico i.val j.val, ε := by
      apply edist_le_Ico_sum_of_edist_le hij
      intro k hik hkj
      have hkpow : k < 2 ^ n := lt_of_lt_of_le hkj (Nat.le_of_lt_succ j.isLt)
      have hksucc : k + 1 < 2 ^ n + 1 := Nat.add_lt_add_right hkpow 1
      rw [hf k (lt_trans hkpow (Nat.lt_succ_self _)), hf (k + 1) hksucc]
      simpa only [Fin.val_castSucc, Fin.val_succ] using! hadj ⟨k, hkpow⟩
    _ = (j.val - i.val : ℕ) * ε := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
