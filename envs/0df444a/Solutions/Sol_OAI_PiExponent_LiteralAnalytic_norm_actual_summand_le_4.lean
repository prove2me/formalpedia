-- Prove2me | solution 4 for OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:56:59.661179+00:00
-- url     : https://prove2.me/submissions/a9c854e2-4c48-4a64-92d1-1367f15480d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_scalar_product_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_le_indexWeight_of_ne_zero
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_low_transverse_capacity
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_lowIndexCount_pos
import Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_translated_summand_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_rowWeight_eq
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_indexWeight_nonneg
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det‖ ≤
    Real.exp ((actualRowCount d H : ℝ) * H *
      (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  by_cases hs : (∏ r, choiceScalar d r (f r)) = 0
  · simp [hs, Real.exp_nonneg]
  have hmono : (actualRowCount d H : ℝ) * H * actualMean d H ≤
      ∑ r, indexWeight d (f r).1 := by
    rw [← sum_rowWeight_eq d hH]
    apply Finset.sum_le_sum
    intro r _
    apply rowWeight_le_indexWeight_of_ne_zero d r (f r)
    exact Finset.prod_ne_zero_iff.mp hs r (Finset.mem_univ r)
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (fun r => (f r).1) (fun A : Transverse d H => indexWeight d A)
    (∏ r, choiceScalar d r (f r)) (choiceMatrix d selection f).det
    hH d.base.A_pos.le d.base.eta_pos.le hnu collisionConstant_pos.le
    (by exact_mod_cast lowIndexCount_pos d hH)
    (indexWeight_nonneg d) hmono (low_transverse_capacity d H)
    (norm_scalar_product_le d hnu hH f) (norm_choiceMatrix_le d hH selection f)
  convert! hb using 1
  congr 1
  unfold AdmissibleParameters.analyticError collisionRate collisionConstant actualRowCount
  ring_nf
