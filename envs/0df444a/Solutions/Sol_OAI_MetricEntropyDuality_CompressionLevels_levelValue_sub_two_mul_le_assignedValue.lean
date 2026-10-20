-- Prove2me | solution 1 for OAI.MetricEntropyDuality.CompressionLevels.levelValue_sub_two_mul_le_assignedValue
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:54:00.103311+00:00
-- url     : https://prove2.me/submissions/602294c0-b4b7-4154-9ad2-f4cccd2122cd

import Mathlib
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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.CompressionLevels
universe uX uY uK uι uLabel
open scoped BigOperators Classical
variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}
variable [Fintype Y]
theorem h51b_ball
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (i : ι) (j : ℕ) (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) (y : Y) :
    ballIndicator L (T y) j x (v y) ≤
      assignedIndicator L T rep assignment j x y +
        (if i ∉ T y then 1 else 0) +
        (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by
  have hb0 : ∀ (S : Finset ι) (k : ℕ) (a b : X), 0 ≤ ballIndicator L S k a b := by
    intro S k a b
    unfold ballIndicator
    split_ifs <;> norm_num
  have hb1 : ballIndicator L (T y) j x (v y) ≤ 1 := by
    unfold ballIndicator
    split_ifs <;> norm_num
  have hA0 : 0 ≤ assignedIndicator L T rep assignment j x y := by
    rcases hk : assignment y with _ | k <;> simp only [assignedIndicator, hk]
    · exact le_refl _
    · exact hb0 _ _ _ _
  have hi0 : (0:ℝ) ≤ (if i ∉ T y then 1 else 0) := by split_ifs <;> norm_num
  have hn0 : (0:ℝ) ≤ (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by split_ifs <;> norm_num
  by_cases hi : i ∈ T y
  · by_cases hn : PartitionGraph.near L (T y) j x (v y)
    · rcases hk : assignment y with _ | k
      · have : (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          (none : Option K) = none then (1:ℝ) else 0) = 1 := if_pos ⟨hi, hn, rfl⟩
        rw [this]
        have : (0:ℝ) ≤ (if i ∉ T y then 1 else 0) := by split_ifs <;> norm_num
        have : assignedIndicator L T rep (fun _ => none) j x y = 0 := rfl
        simp only [assignedIndicator, hk]
        linarith
      · obtain ⟨-, hc⟩ := hassign y k hk
        have h1 : (PartitionGraph.graph L (T y)).edist x (v y) ≤ j := hn
        have h2 : (PartitionGraph.graph L (T y)).edist (v y) (centers k) ≤ j := by
          rw [SimpleGraph.edist_comm]
          exact hc
        have h3 : (PartitionGraph.graph L (T y)).edist (centers k) (rep k) ≤ 1 := by
          by_cases he : centers k = rep k
          · rw [he]
            simp
          · rw [(SimpleGraph.edist_eq_one_iff_adj).mpr
              (by exact ⟨he, i, hi, (hrep k).symm⟩ :
                (PartitionGraph.graph L (T y)).Adj (centers k) (rep k))]
        have hnear : PartitionGraph.near L (T y) (2 * j + 1) x (rep k) := by
          show (PartitionGraph.graph L (T y)).edist x (rep k) ≤ ((2 * j + 1 : ℕ) : ℕ∞)
          calc (PartitionGraph.graph L (T y)).edist x (rep k)
              ≤ (PartitionGraph.graph L (T y)).edist x (v y) +
                  (PartitionGraph.graph L (T y)).edist (v y) (rep k) :=
                SimpleGraph.edist_triangle
            _ ≤ (PartitionGraph.graph L (T y)).edist x (v y) +
                  ((PartitionGraph.graph L (T y)).edist (v y) (centers k) +
                    (PartitionGraph.graph L (T y)).edist (centers k) (rep k)) :=
                add_le_add le_rfl SimpleGraph.edist_triangle
            _ ≤ (j : ℕ∞) + ((j : ℕ∞) + 1) := add_le_add h1 (add_le_add h2 h3)
            _ = ((2 * j + 1 : ℕ) : ℕ∞) := by push_cast; ring
        have : assignedIndicator L T rep assignment j x y = 1 := by
          simp only [assignedIndicator, hk, ballIndicator, if_pos hnear]
        rw [this]
        have : (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          (some k : Option K) = none then (1:ℝ) else 0) = 0 := if_neg (by simp)
        rw [this]
        linarith
    · have : ballIndicator L (T y) j x (v y) = 0 := by simp [ballIndicator, hn]
      rw [this]
      linarith
  · have : (if i ∉ T y then (1:ℝ) else 0) = 1 := if_pos hi
    rw [this]
    linarith

theorem solution
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (i : ι) (j : ℕ)
    (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) {θ : ℝ}
    (homit : (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ)
    (hrem : ∀ x, (∑ y ∈ Finset.univ.filter (fun y =>
      i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
        assignment y = none), μ y) ≤ θ) (x : X) :
    levelValue L v T μ j x - 2 * θ ≤ assignedValue L T rep assignment μ j x := by
  have e1 : (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) =
      ∑ y, μ y * (if i ∉ T y then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have e2 : (∑ y ∈ Finset.univ.filter (fun y =>
      i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧ assignment y = none), μ y) =
      ∑ y, μ y * (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have h1 := homit
  have h2 := hrem x
  rw [e1] at h1
  rw [e2] at h2
  have key : levelValue L v T μ j x ≤ assignedValue L T rep assignment μ j x +
      ∑ y, μ y * (if i ∉ T y then 1 else 0) +
      ∑ y, μ y * (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by
    unfold levelValue assignedValue
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [← mul_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left
      (h51b_ball L v T i j centers rep assignment hassign hrep x y) (hμ y)
  linarith

