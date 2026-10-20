-- Prove2me | solution 2 for OAI.MetricEntropyDuality.coverable_of_isCompact_of_mem_nhds_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:43:38.33805+00:00
-- url     : https://prove2.me/submissions/0a2613e3-ecad-48d9-8b07-0e4db1a8474e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CoveringNumber.lean:L102-L119
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.coverable_of_isCompact_of_mem_nhds_zero. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.CoveringNumber ----
namespace OAI

universe uι uJ uX

/-!
# Finite covering numbers and the cube packing bound

Centers are arbitrary ambient vectors throughout. Attainment and lower bounds
explicitly assume a finite cover exists, because the natural-number infimum of
the empty set is zero. Compactness and a neighborhood of zero supply that
hypothesis in the geometric application.
-/

noncomputable section

namespace MetricEntropyDuality

open Set Filter
open scoped Topology

variable {ι : Type uι} {A A' B B' : Set (RealSpace ι)}

/-- Enumerate a finite set of indices, retaining exactly its cardinality. -/
theorem exists_finset_cover {J : Type uJ} (s : Finset J)
    (c : J → RealSpace ι) (hc : ∀ x ∈ A, ∃ j ∈ s, x - c j ∈ B) :
    ∃ d : Fin s.card → RealSpace ι, Covers A B d := by
  classical
  refine ⟨fun j => c (s.equivFin.symm j), ?_⟩
  intro x hx
  obtain ⟨j, hj, hcov⟩ := hc x hx
  exact ⟨s.equivFin ⟨j, hj⟩, by simpa only [Equiv.symm_apply_apply] using hcov⟩

/-- Translates of any neighborhood of zero finitely cover a compact set. -/
theorem coverable_of_isCompact_of_mem_nhds_zero (hA : IsCompact A)
    (hB : B ∈ 𝓝 (0 : RealSpace ι)) : Coverable A B := by
  classical
  let U : RealSpace ι → Set (RealSpace ι) := fun x => {y | y - x ∈ B}
  have hU : ∀ x ∈ A, U x ∈ 𝓝 x := by
    intro x _
    have hc : ContinuousAt (fun y : RealSpace ι => y - x) x :=
      continuousAt_id.sub continuousAt_const
    exact hc.preimage_mem_nhds (by simpa only [sub_self] using hB)
  obtain ⟨s, _, hs⟩ := hA.elim_nhds_subcover U hU
  have hcov : ∀ x ∈ A, ∃ j ∈ s, x - j ∈ B := by
    intro x hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨hjs, hmem⟩ := Set.mem_iUnion.mp hj
    exact ⟨j, hjs, hmem⟩
  obtain ⟨c, hc⟩ := exists_finset_cover s (fun x => x) hcov
  exact ⟨s.card, c, hc⟩

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open Set Filter
open scoped Topology


theorem solution.{uι} : type_of% @_root_.OAI.MetricEntropyDuality.coverable_of_isCompact_of_mem_nhds_zero.{uι} := @_root_.OAI.MetricEntropyDuality.coverable_of_isCompact_of_mem_nhds_zero.{uι}
