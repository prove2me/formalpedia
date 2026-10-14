-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.transverseIndices_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T16:38:42.865931+00:00
-- url     : https://prove2.me/submissions/1bc2fc34-d0fe-44b3-87f0-4d111733148e

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

theorem solution {nu : ℝ}
    (d : FixedData nu) (H : ℝ)
    (a : MatrixTranslation.transverseIndices (fixedWeights d) H)
    (i : Fin d.m) :
    a.1 i < ⌊H⌋₊ + 1 := by
  classical
  have hmem : a.1 ∈ (realWeightedSimplex (fixedWeights d) H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding := by
    change a.1 ∈ MatrixTranslation.transverseIndices (fixedWeights d) H
    exact a.2
  rcases Finset.mem_map.mp hmem with ⟨b, hb, hmap⟩
  have hb' := hb
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range] at hb'
  have hcoord : b i = a.1 i := by
    have hmap' := congrArg Finsupp.equivFunOnFinite hmap
    simpa using congrFun hmap' i
  have hw : 1 ≤ fixedWeights d i := by
    have heq : fixedWeights d i = d.x (i.val + 1) := by
      simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
    rw [heq]
    exact d.x_one_le _
  have hsum_nonneg : 0 ≤ ∑ j : Fin d.m, fixedWeights d j * (b j : ℝ) := by
    apply Finset.sum_nonneg
    intro j hj
    have hwj : 0 ≤ fixedWeights d j := by
      have heq : fixedWeights d j = d.x (j.val + 1) := by
        simp only [fixedWeights, MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
      rw [heq]
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (d.x_one_le _)
    exact mul_nonneg hwj (Nat.cast_nonneg _)
  have hH : 0 ≤ H := le_trans hsum_nonneg hb'.2
  have hdiv : H / fixedWeights d i ≤ H := div_le_self hH hw
  have hfloor : ⌊H / fixedWeights d i⌋₊ ≤ ⌊H⌋₊ := Nat.floor_mono hdiv
  have hlt : b i < ⌊H / fixedWeights d i⌋₊ + 1 := hb'.1 i
  rw [← hcoord]
  omega
