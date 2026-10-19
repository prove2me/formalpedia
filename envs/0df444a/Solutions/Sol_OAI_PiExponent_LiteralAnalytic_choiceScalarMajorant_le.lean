-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choiceScalarMajorant_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:28:50.838304+00:00
-- url     : https://prove2.me/submissions/f2cf205b-f0ad-4a62-b440-0fba580bc335

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
import Definitions.Def_OAI_PiExponent_LiteralAnalytic_choiceScalarMajorant

import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_norm_rowScalar_exp_weight_difference
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_actual_error_exp

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction
open Filter

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    choiceScalarMajorant d r t ≤ Real.exp (H * d.translationError) *
      Real.exp (-nu * ∑ i : Fin d.m, fixedWeights d i *
        ((t.1.1 i : ℝ) - (beta d r i : ℝ))) := by
  classical
  have hw_eq (i : Fin d.m) : fixedWeights d i = d.x (i.val + 1) := by
    change (⌈Real.log (d.q i.val)⌉₊ : ℝ) = d.x (i.val + 1)
    exact (d.x_log i.val).symm
  have hw (i : Fin d.m) : d.wstar ≤ fixedWeights d i := by
    rw [hw_eq]
    exact d.wstar_lower i
  have hwpos (i : Fin d.m) : 0 < fixedWeights d i :=
    d.wstar_pos.trans_le (hw i)
  have hrowweights (i : Fin (d.m + 1)) :
      0 ≤ InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i := by
    cases i using Fin.cases with
    | zero => exact d.v0_pos.le
    | succ i => exact div_nonneg (hwpos i).le d.base.theta_pos.le
  have hr : (∑ i : Fin (d.m + 1),
      InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i *
        (r.2.1 i : ℝ)) < H :=
    (Finset.mem_filter.mp r.2.2).2
  have hs : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤
      ∑ i : Fin (d.m + 1),
        InterpolationMatrix.rowWeights d.v0 d.base.theta (fixedWeights d) i *
          (r.2.1 i : ℝ) :=
    Finset.single_le_sum
      (fun i _ => mul_nonneg (hrowweights i) (Nat.cast_nonneg _))
      (Finset.mem_univ (0 : Fin (d.m + 1)))
  have horder : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply le_trans _ horder
    exact_mod_cast Nat.le_of_lt_succ t.2.2.isLt
  have ha : MatrixTranslationBounds.weight (fixedWeights d)
      (fun i => t.1.1 i) ≤ H := by
    have hm := t.1.2
    change t.1.1 ∈ (realWeightedSimplex (fixedWeights d) H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding at hm
    have hm' : Finsupp.equivFunOnFinite t.1.1 ∈
        realWeightedSimplex (fixedWeights d) H := by
      simpa only [Finset.mem_map_equiv, Equiv.symm_symm] using hm
    have hcoe : Finsupp.equivFunOnFinite t.1.1 = (fun i => t.1.1 i) := rfl
    rw [hcoe] at hm'
    exact (Finset.mem_filter.mp hm').2
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu :=
    add_nonneg (Real.log_nonneg (by linarith)) hnu
  have hT : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders
      (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    exact Nat.ceil_pos.mpr (div_pos (mul_pos d.F0_pos (hwpos i)) d.v0_pos)
  have hTw : ∀ i, d.F0 * fixedWeights d i ≤ (d.v0 : ℝ) *
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    have hh := (div_le_iff₀ d.v0_pos).mp
      (Nat.le_ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)))
    simpa only [MatrixArithmetic.truncationOrders, fixedWeights, mul_comm] using hh
  have heps := OAI.PiExponent.MatrixTranslationBounds.actual_error_exp
    (finiteNumerators d) (finiteDenominators d) r.1.val d.K nu d.K_pos
    r.1.isLt.le hnu
    (fun i => le_trans (by decide : 1 ≤ 2) (d.approximations i.val).1)
    (fun i => (d.approximations i.val).2.2)
  have hb := OAI.PiExponent.MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
        logarithmicPeriod))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (beta d r) t.1.1 t.2.1 t.2.2 (fixedWeights d)
    (Real.log (2 * (d.K : ℝ)) + nu) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos hw ha hk hT hTw heps
  have hmajor : choiceScalarMajorant d r t = ‖choiceScalar d r t‖ := by
    simp only [choiceScalarMajorant, choiceScalar, RowTranslation.rowScalar,
      norm_mul, norm_prod, norm_pow, Complex.norm_natCast]
  have hweight :
      indexWeight d t.1 - rowWeight d r =
        ∑ i : Fin d.m, fixedWeights d i *
          ((t.1.1 i : ℝ) - (beta d r i : ℝ)) := by
    simp only [indexWeight, rowWeight, MatrixTranslationBounds.weight,
      mul_sub, Finset.sum_sub_distrib]
  rw [hmajor]
  calc
    ‖choiceScalar d r t‖ ≤
        Real.exp (-nu * (indexWeight d t.1 - rowWeight d r) +
          H * d.translationError) := by
      simpa only [choiceScalar, indexWeight, rowWeight,
        AdmissibleParameters.translationError, add_assoc] using hb
    _ = Real.exp (H * d.translationError) *
        Real.exp (-nu * ∑ i : Fin d.m, fixedWeights d i *
          ((t.1.1 i : ℝ) - (beta d r i : ℝ))) := by
      rw [hweight, add_comm, Real.exp_add]
