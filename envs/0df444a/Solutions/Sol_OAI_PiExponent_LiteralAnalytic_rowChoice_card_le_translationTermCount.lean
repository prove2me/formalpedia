-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowChoice_card_le_translationTermCount
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:53:48.665088+00:00
-- url     : https://prove2.me/submissions/867b5806-17a1-4b24-8dbc-1d21779638f0

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_RowTranslation_rowChoices_card_le_box_product
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_transverseIndex_count_bounds

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) (r : Row d H) :
    Fintype.card (RowChoice d H r) ≤ translationTermCount d.m d.v0 H := by
  classical
  let N : ℕ := ⌊H⌋₊ + 1
  let T : ℕ := ⌊H / d.v0⌋₊ + 1
  have hb := OAI.PiExponent.LiteralAnalytic.transverseIndex_count_bounds d H r
  have hbox := (hb.2.1)
  have hrow := hb.2.2
  have hc := OAI.PiExponent.RowTranslation.rowChoices_card_le_box_product
    (MatrixTranslation.transverseIndices (fixedWeights d) H) (beta d r)
    (r.2.1 0) N hbox
  have hc' : Fintype.card (RowChoice d H r) ≤
      Fintype.card (MatrixTranslation.transverseIndices (fixedWeights d) H) *
        N ^ d.m * (r.2.1 0 + 1) := by
    simpa [RowChoice, Fintype.card_fin] using hc
  change Fintype.card (RowChoice d H r) ≤ _
  unfold RowChoice
  dsimp [N, T] at *
  calc
    Fintype.card
        (RowTranslation.RowChoices
          (MatrixTranslation.transverseIndices (fixedWeights d) H)
          (beta d r) (r.2.1 0))
        ≤ Fintype.card (MatrixTranslation.transverseIndices (fixedWeights d) H) *
            (⌊H⌋₊ + 1) ^ d.m * (r.2.1 0 + 1) := hc'
    _ ≤ (⌊H⌋₊ + 1) ^ d.m * (⌊H⌋₊ + 1) ^ d.m *
          (⌊H / d.v0⌋₊ + 1) := by
      calc
        _ ≤ (⌊H⌋₊ + 1) ^ d.m * (⌊H⌋₊ + 1) ^ d.m * (r.2.1 0 + 1) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb.1)
        _ ≤ (⌊H⌋₊ + 1) ^ d.m * (⌊H⌋₊ + 1) ^ d.m *
              (⌊H / d.v0⌋₊ + 1) := Nat.mul_le_mul_left _ hrow
    _ = translationTermCount d.m d.v0 H := by
      unfold translationTermCount
      calc
        (⌊H⌋₊ + 1) ^ d.m * (⌊H⌋₊ + 1) ^ d.m * (⌊H / d.v0⌋₊ + 1) =
            (⌊H⌋₊ + 1) ^ (2 * d.m) * (⌊H / d.v0⌋₊ + 1) := by
          rw [← pow_add]
          congr 2 <;> omega
        _ = (⌊H⌋₊ + 1) ^ (2 * d.m) * (⌊H / d.v0⌋₊ + 1) := rfl
