-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choice_scalar_weight_inputs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T13:24:41.728759+00:00
-- url     : https://prove2.me/submissions/99cdbfa5-75ba-4a11-a353-d81708e4bc08

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

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (t : RowChoice d H r) :
    0 < d.wstar ∧ 0 < (d.v0 : ℝ) ∧ 0 < d.F0 ∧
    (∀ i, d.wstar ≤ fixedWeights d i) ∧
    MatrixTranslationBounds.weight (fixedWeights d) (fun i => t.1.1 i) ≤ H ∧
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) ∧
    (∀ i, 1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i, d.F0 * fixedWeights d i ≤ (d.v0 : ℝ) *
      MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by
  classical
  have hw : ∀ i : Fin d.m, 0 < fixedWeights d i := by
    intro i
    have heq : fixedWeights d i = d.x (i.val + 1) := by
      simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
    rw [heq]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hwstar : ∀ i : Fin d.m, d.wstar ≤ fixedWeights d i := by
    intro i
    have heq : fixedWeights d i = d.x (i.val + 1) := by
      simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
    rw [heq]
    exact d.wstar_lower i
  have hchoice : MatrixTranslationBounds.weight (fixedWeights d) (fun i => t.1.1 i) ≤ H := by
    have hmem : t.1.1 ∈ MatrixTranslation.transverseIndices (fixedWeights d) H := t.1.property
    change t.1.1 ∈ (realWeightedSimplex (fixedWeights d) H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding at hmem
    rcases Finset.mem_map.mp hmem with ⟨a, ha, hmap⟩
    have hsum : ∑ i, fixedWeights d i * (a i : ℝ) ≤ H := by
      exact (Finset.mem_filter.mp ha).2
    have hval : ∀ i, a i = t.1.1 i := by
      intro i
      have hmap' := congrArg Finsupp.equivFunOnFinite hmap
      simpa using congrFun hmap' i
    calc
      MatrixTranslationBounds.weight (fixedWeights d) (fun i => t.1.1 i) =
          ∑ i, fixedWeights d i * (a i : ℝ) := by
        simp only [MatrixTranslationBounds.weight]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hval i]
      _ ≤ H := hsum
  have hrow_strict :
      ∑ j : Fin (d.m + 1), InterpolationMatrix.rowWeights d.v0 d.base.theta
        (fixedWeights d) j * (r.2.1 j : ℝ) < H := by
    exact (Finset.mem_filter.mp r.2.property).2
  have htail_nonneg :
      0 ≤ ∑ i : Fin d.m, (fixedWeights d i / (d.base.theta : ℝ)) *
        (r.2.1 i.succ : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (div_nonneg (hw i).le d.base.theta_pos.le) (Nat.cast_nonneg _)
  have hscalar : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤ H := by
    have hdecomp :
        (∑ j : Fin (d.m + 1), InterpolationMatrix.rowWeights d.v0 d.base.theta
          (fixedWeights d) j * (r.2.1 j : ℝ)) =
        (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
          ∑ i : Fin d.m, (fixedWeights d i / (d.base.theta : ℝ)) *
            (r.2.1 i.succ : ℝ) := by
      simp [InterpolationMatrix.rowWeights, Fin.sum_univ_succ]
    rw [hdecomp] at hrow_strict
    linarith
  have hchoice_scalar : (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) := by
    have htval : t.2.2 ≤ r.2.1 0 := Nat.le_of_lt_succ t.2.2.isLt
    apply (le_div_iff₀ d.v0_pos).2
    have htval' : (t.2.2 : ℝ) ≤ (r.2.1 0 : ℝ) := by exact_mod_cast htval
    have hmul : (t.2.2 : ℝ) * (d.v0 : ℝ) ≤ H := by
      calc
        (t.2.2 : ℝ) * (d.v0 : ℝ) ≤ (r.2.1 0 : ℝ) * (d.v0 : ℝ) :=
          mul_le_mul_of_nonneg_right htval' d.v0_pos.le
        _ = (d.v0 : ℝ) * (r.2.1 0 : ℝ) := by ring
        _ ≤ H := hscalar
    exact hmul
  have htrunc_pos : ∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    have harg : 0 < d.F0 * fixedWeights d i / (d.v0 : ℝ) :=
      div_pos (mul_pos d.F0_pos (hw i)) d.v0_pos
    change 1 ≤ Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ))
    have hceilpos : 0 < (Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)) : ℝ) :=
      lt_of_lt_of_le harg (Nat.le_ceil _)
    have hceilpos' : 0 < Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)) := by
      exact_mod_cast hceilpos
    omega
  have htrunc_budget : ∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤ (d.v0 : ℝ) *
        MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    intro i
    have hceil := Nat.le_ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ))
    change d.F0 * fixedWeights d i ≤ (d.v0 : ℝ) *
      (Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)) : ℝ)
    calc
      d.F0 * fixedWeights d i ≤
          (Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)) : ℝ) * (d.v0 : ℝ) :=
        (div_le_iff₀ d.v0_pos).mp hceil
      _ = (d.v0 : ℝ) *
          (Nat.ceil (d.F0 * fixedWeights d i / (d.v0 : ℝ)) : ℝ) := by ring
  exact ⟨d.wstar_pos, d.v0_pos, d.F0_pos, hwstar, hchoice, hchoice_scalar,
    htrunc_pos, htrunc_budget⟩
