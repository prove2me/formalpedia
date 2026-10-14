-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.card_choiceFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T09:43:51.42392+00:00
-- url     : https://prove2.me/submissions/06af9ce3-70c4-4271-814e-0d9766c76af3

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowChoice_card_le_translationTermCount

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [show actualRowCount d H = Fintype.card (Row d H) by rfl]
  rw [Fintype.card_pi]
  calc
    ∏ r : Row d H, Fintype.card (RowChoice d H r) ≤
        ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod (fun r hr => Nat.zero_le _)
      intro r hr
      exact OAI.PiExponent.LiteralAnalytic.rowChoice_card_le_translationTermCount d H r
    _ = translationTermCount d.m d.v0 H ^ Fintype.card (Row d H) := by
      simp
