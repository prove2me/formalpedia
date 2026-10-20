-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_common_index
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:08:04.038865+00:00
-- url     : https://prove2.me/submissions/9c097d3e-fd32-4e26-a926-7770f997e91e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CommonIndex.lean:L47-L69
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_common_index. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_sum_omitted_mass

-- ---- from OAI.Analysis.MetricEntropy.CommonIndex ----
namespace OAI

universe uY

/-!
# A common index for all compression levels

For nonnegative column weights of total mass at most one, an average bound
on the number of indices omitted by each column gives one index whose
omitted mass is at most the same bound. No level parameter enters the
selection, so this index can be used at every approximation level.
-/

namespace MetricEntropyDuality

open scoped BigOperators

/-- One index has omitted mass at most `θ`; it is chosen before all levels. -/
theorem exists_common_index {Y : Type uY} [Fintype Y] {u : ℕ}
    (hu : 0 < u) (T : Y → Finset (Fin u)) (μ : Y → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ i : Fin u, (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ := by
  classical
  have hsum :
      (∑ i : Fin u, ∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤
        ∑ _i : Fin u, θ := by
    calc
      _ = ∑ y, μ y * ((Finset.univ \ T y).card : ℝ) := sum_omitted_mass T μ
      _ ≤ ∑ y, μ y * (θ * (u : ℝ)) := by
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hcomp y) (hμ y)
      _ = (∑ y, μ y) * (θ * (u : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (θ * (u : ℝ)) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg hθ (Nat.cast_nonneg u))
      _ = ∑ _i : Fin u, θ := by simp [nsmul_eq_mul, mul_comm]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin u)).Nonempty from
      ⟨⟨0, hu⟩, Finset.mem_univ _⟩) hsum
  exact ⟨i, hi⟩

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators


theorem solution.{uY} : type_of% @_root_.OAI.MetricEntropyDuality.exists_common_index.{uY} := @_root_.OAI.MetricEntropyDuality.exists_common_index.{uY}
