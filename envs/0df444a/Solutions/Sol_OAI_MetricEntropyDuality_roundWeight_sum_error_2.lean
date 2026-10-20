-- Prove2me | solution 2 for OAI.MetricEntropyDuality.roundWeight_sum_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:18:03.724517+00:00
-- url     : https://prove2.me/submissions/4e959ce3-1248-463f-8520-a393ef3b0391

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/WeightRounding.lean:L98-L117
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.roundWeight_sum_error. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding

-- ---- from OAI.Analysis.MetricEntropy.WeightRounding ----
namespace OAI

universe uI

/-!
# Finite codes for downward rounding of grouped weights

For a positive mesh `δ`, a weight in `[0, 1]` is rounded down to
`δ * floor (w / δ)`. Its integer coefficient is an actual element of
`Fin (floor (1 / δ) + 1)`, including the possible endpoint `w = 1`.
The error estimates apply to every indicator with values in `[0, 1]`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

theorem roundWeight_le {δ w : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w) :
    roundWeight δ w ≤ w := by
  have hf := Nat.floor_le (div_nonneg hw0 hδ.le)
  have hm := (le_div_iff₀ hδ).mp hf
  simpa only [roundWeight, mul_comm] using hm

/-- The downward rounding error is strictly smaller than one mesh interval. -/
theorem roundWeight_sub_lt {δ w : ℝ} (hδ : 0 < δ) :
    w - roundWeight δ w < δ := by
  have hf := Nat.lt_floor_add_one (w / δ)
  have hm := (div_lt_iff₀ hδ).mp hf
  dsimp [roundWeight]
  nlinarith

theorem roundWeight_error {δ w : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w) :
    0 ≤ w - roundWeight δ w ∧ w - roundWeight δ w < δ :=
  ⟨sub_nonneg.mpr (roundWeight_le hδ hw0), roundWeight_sub_lt hδ⟩

/-- Multiplying by a number in `[0, 1]` cannot increase the rounding loss. -/
theorem roundWeight_mul_error {δ w b : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ w * b - roundWeight δ w * b ∧
      w * b - roundWeight δ w * b ≤ δ := by
  rw [← sub_mul]
  have herr := roundWeight_error hδ hw0
  exact ⟨mul_nonneg herr.1 hb0,
    (mul_le_of_le_one_right herr.1 hb1).trans herr.2.le⟩

/-- Simultaneous rounding of an actual finite array of weights loses at most
one mesh interval for each array entry. -/
theorem roundWeight_sum_error {I : Type uI} [Fintype I]
    (δ : ℝ) (hδ : 0 < δ) (w b : I → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    0 ≤ (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ∧
      (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ≤
        (Fintype.card I : ℝ) * δ := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => (roundWeight_mul_error hδ (hw0 i) (hb0 i) (hb1 i)).1
  · calc
      (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i =
          ∑ i, (w i * b i - roundWeight δ (w i) * b i) :=
        (Finset.sum_sub_distrib (s := Finset.univ)
          (fun i : I => w i * b i)
          (fun i : I => roundWeight δ (w i) * b i)).symm
      _ ≤ ∑ _i : I, δ := Finset.sum_le_sum fun i _ =>
        (roundWeight_mul_error hδ (hw0 i) (hb0 i) (hb1 i)).2
      _ = (Fintype.card I : ℝ) * δ := by simp

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators


theorem solution.{uI} : type_of% @_root_.OAI.MetricEntropyDuality.roundWeight_sum_error.{uI} := @_root_.OAI.MetricEntropyDuality.roundWeight_sum_error.{uI}
