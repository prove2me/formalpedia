-- Prove2me | solution 1 for OAI.TalagrandThreshold.one_sub_sum_le_prod_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:05:39.153237+00:00
-- url     : https://prove2.me/submissions/c5f3e0f9-fb66-4135-915e-b1baf4b422c0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/TupleCoefficients.lean:L70-L86
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.one_sub_sum_le_prod_one_sub. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients

-- ---- from OAI.Combinatorics.ExpectationThreshold.TupleCoefficients ----
namespace OAI

/-!
# Coefficients for the finite tuple estimate

Replacing `e` by `3` gives the coefficients `3 / 64^(i+1)`. Their finite
sum has an explicit positive remainder below `1 / 21`. A finite product
inequality then bounds the product of their complements from below.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- A finite product loses at most the sum of its factors' deficits. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (h0 : ∀ i, 0 ≤ c i) (h1 : ∀ i, c i ≤ 1) :
    1 - ∑ i, c i ≤ ∏ i, (1 - c i) := by
  classical
  suffices h : ∀ s : Finset ι,
      1 - ∑ i ∈ s, c i ≤ ∏ i ∈ s, (1 - c i) by
    exact h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, c i :=
      Finset.sum_nonneg (fun i _ => h0 i)
    have hm := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (h1 a))
    nlinarith [mul_nonneg (h0 a) hs]

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.one_sub_sum_le_prod_one_sub := @_root_.OAI.TalagrandThreshold.one_sub_sum_le_prod_one_sub
