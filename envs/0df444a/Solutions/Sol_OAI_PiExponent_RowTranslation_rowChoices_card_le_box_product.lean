-- Prove2me | solution 1 for OAI.PiExponent.RowTranslation.rowChoices_card_le_box_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:44:34.792223+00:00
-- url     : https://prove2.me/submissions/0bfae2bc-e160-4145-86c9-9cd60a9a9bdd

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

open OAI.PiExponent.RowTranslation

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s N : ℕ)
    (hbox : ∀ a ∈ S, ∀ i, a i < N) :
    Fintype.card (RowChoices S β s) ≤
      Fintype.card S * N ^ Fintype.card σ * (s + 1) := by
  classical
  calc
    Fintype.card (RowChoices S β s) =
        ∑ a : S, Fintype.card ((∀ i, Fin (a.1 i - β i + 1)) × Fin (s + 1)) := by
      simp [RowChoices, Fintype.card_sigma]
    _ ≤ ∑ a : S, (N ^ Fintype.card σ) * (s + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      have hcoord : ∀ i : σ, a.1 i - β i + 1 ≤ N := by
        intro i
        have hi := hbox a.1 a.2 i
        omega
      have hpi : Fintype.card (∀ i : σ, Fin (a.1 i - β i + 1)) ≤ N ^ Fintype.card σ := by
        calc
          Fintype.card (∀ i : σ, Fin (a.1 i - β i + 1)) =
              ∏ i : σ, (a.1 i - β i + 1) := by simp
          _ ≤ ∏ i : σ, N := by
            apply Finset.prod_le_prod
            · intro i hi
              exact Nat.zero_le _
            · intro i hi
              exact hcoord i
          _ = N ^ Fintype.card σ := by simp
      simpa [Fintype.card_prod] using Nat.mul_le_mul_right (s + 1) hpi
    _ = Fintype.card S * N ^ Fintype.card σ * (s + 1) := by
      simp [mul_assoc]