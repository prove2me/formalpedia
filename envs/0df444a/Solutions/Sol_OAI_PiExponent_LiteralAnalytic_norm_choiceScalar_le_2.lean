-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.norm_choiceScalar_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T15:44:42.095978+00:00
-- url     : https://prove2.me/submissions/87797a7b-bb08-4b59-a828-91b9351ee5e2

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_fixedWeights_pos
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_actual_error_exp
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_norm_rowScalar_exp_weight_difference
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
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu :=
    add_nonneg (Real.log_nonneg (by linarith)) hnu
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    have hr : d.v0 * (r.2.1 0 : ℝ) +
        (∑ i : Fin d.m, (fixedWeights d i / d.base.theta) *
          (r.2.1 i.succ : ℝ)) < H := by
      have hmem := (Finset.mem_filter.mp r.2.2).2
      simpa [fixedWeights, InterpolationMatrix.rowWeights, Fin.sum_univ_succ] using hmem
    have hsum : 0 ≤ (∑ i : Fin d.m,
        (fixedWeights d i / d.base.theta) * (r.2.1 i.succ : ℝ)) := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (div_nonneg (fixedWeights_pos d i).le d.base.theta_pos.le)
        (Nat.cast_nonneg _)
    have ht : ((t.2.2 : ℕ) : ℝ) ≤ (r.2.1 0 : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
    have hscale := mul_le_mul_of_nonneg_left ht d.v0_pos.le
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith [hscale]
  have hT : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    change 1 ≤ ⌈d.F0 * fixedWeights d i / d.v0⌉₊
    exact Nat.ceil_pos.mpr (div_pos (mul_pos d.F0_pos (fixedWeights_pos d i)) d.v0_pos)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤
      (d.v0 : ℝ) * MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    change d.F0 * fixedWeights d i ≤ d.v0 * (⌈d.F0 * fixedWeights d i / d.v0⌉₊ : ℝ)
    have hceil : d.F0 * fixedWeights d i / d.v0 ≤
        (⌈d.F0 * fixedWeights d i / d.v0⌉₊ : ℝ) := Nat.le_ceil _
    simpa only [mul_comm] using (div_le_iff₀ d.v0_pos).mp hceil
  have heps := MatrixTranslationBounds.actual_error_exp (finiteNumerators d) (finiteDenominators d)
    r.1.val d.K nu d.K_pos r.1.isLt.le hnu
    (fun i => le_trans (by decide : 1 ≤ 2)
      (show 2 ≤ finiteDenominators d i from (d.approximations i.val).1))
    (fun i => (d.approximations i.val).2.2)
  have hWL : ∀ i : Fin d.m, d.wstar ≤ fixedWeights d i := by
    intro i
    change d.wstar ≤ (⌈Real.log (d.q i.val)⌉₊ : ℝ)
    rw [← d.x_log i.val]
    exact d.wstar_lower i
  have hindex : indexWeight d t.1 ≤ H := by
    change (∑ i : Fin d.m, fixedWeights d i * (t.1.1 i : ℝ)) ≤ H
    have hm : t.1.1 ∈ MatrixTranslation.transverseIndices (fixedWeights d) H := t.1.2
    unfold MatrixTranslation.transverseIndices at hm
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hm
    have hweight : (∑ i : Fin d.m, fixedWeights d i * (a i : ℝ)) ≤ H := by
      exact (Finset.mem_filter.mp ha).2
    have hcoords (i : Fin d.m) : t.1.1 i = a i := by
      have hi := congrArg (fun f : Fin d.m →₀ ℕ => f i) he
      simpa using hi.symm
    simpa only [hcoords] using hweight
  have hb := MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - logarithmicPeriod))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos hWL hindex
    hk hT hTw heps
  simpa only [choiceScalar, indexWeight, rowWeight, AdmissibleParameters.translationError, add_assoc]
    using hb
