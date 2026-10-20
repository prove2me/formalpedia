-- Prove2me | solution 2 for OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:52:18.521311+00:00
-- url     : https://prove2.me/submissions/d3b700b0-ef16-4cc8-81b3-8dfe8dfdadea

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/DirectionDeletion.lean:L23-L90
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.DirectionTuples ----
namespace OAI

universe uU uE

/-!
# Supports and events for direction tuples

Tuples are arbitrary functions from `Fin h`; repeated indices are allowed.
The support records distinct indices, so its cardinality can be smaller than `h`.
-/

namespace MetricEntropyDuality

variable {U : Type uU} {E : Type uE} {h w : ℕ}

theorem tupleSupport_card_le (a : Fin h → U) : (tupleSupport a).card ≤ h := by
  classical
  simpa only [tupleSupport, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_image_le (s := Finset.univ) (f := a))

theorem tupleSupport_nonempty (hh : 0 < h) (a : Fin h → U) :
    (tupleSupport a).Nonempty :=
  ⟨a ⟨0, hh⟩, mem_tupleSupport.mpr ⟨⟨0, hh⟩, rfl⟩⟩

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.DirectionDeletion ----
namespace OAI

universe uU

/-!
# Deleting the supports of a maximal family of bad tuples

The finite powerset construction below chooses a family of maximum cardinality.
Its maximality is proved inside the argument; it is not an input hypothesis.
Repeated indices within any tuple are allowed.
-/

namespace MetricEntropyDuality.DirectionDeletion

open scoped Classical

/-- If there are no `w` bad tuples with pairwise disjoint supports, deleting at
most `h * (w - 1)` indices removes every bad tuple. -/
theorem exists_good_subset {U : Type uU} [Fintype U] {h w : ℕ}
    (bad : (Fin h → U) → Prop) (hh : 0 < h)
    (hno : ¬ ∃ L : Fin w → Fin h → U,
      (∀ i, bad (L i)) ∧ DisjointSupports L) :
    ∃ T : Finset U, (Finset.univ \ T).card ≤ h * (w - 1) ∧
      ∀ a : Fin h → U, (∀ j, a j ∈ T) → ¬bad a := by
  classical
  let valid : Finset (Fin h → U) → Prop := fun F =>
    (∀ a ∈ F, bad a) ∧ (F : Set (Fin h → U)).PairwiseDisjoint tupleSupport
  let candidates := (Finset.univ : Finset (Fin h → U)).powerset.filter valid
  have mem_candidates (F : Finset (Fin h → U)) : F ∈ candidates ↔ valid F := by
    simp [candidates]
  have hempty : (∅ : Finset (Fin h → U)) ∈ candidates := by
    apply (mem_candidates ∅).mpr
    simp [valid]
  obtain ⟨F, hFc, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hF : valid F := (mem_candidates F).mp hFc
  have hcard : F.card < w := by
    by_contra hn
    have hw : w ≤ F.card := Nat.le_of_not_gt hn
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
      (α := Fin w) (s := F) (by simpa using hw)
    apply hno
    refine ⟨fun i => e i, ?_, ?_⟩
    · intro i
      exact hF.1 (e i) (he ⟨i, rfl⟩)
    · intro i j hij
      exact hF.2 (he ⟨i, rfl⟩) (he ⟨j, rfl⟩)
        (fun heq => hij (e.injective heq))
  let deleted := F.biUnion tupleSupport
  have hdeleted : deleted.card ≤ F.card * h :=
    Finset.card_biUnion_le_card_mul F tupleSupport h
      (fun a _ => tupleSupport_card_le a)
  refine ⟨Finset.univ \ deleted, ?_, ?_⟩
  · have hcard' : F.card ≤ w - 1 := Nat.le_sub_one_of_lt hcard
    calc
      (Finset.univ \ (Finset.univ \ deleted)).card = deleted.card := by
        rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
      _ ≤ F.card * h := hdeleted
      _ ≤ h * (w - 1) := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_right h hcard'
  · intro a ha hbad
    have ha_deleted (j : Fin h) : a j ∉ deleted := (Finset.mem_sdiff.mp (ha j)).2
    have haF : a ∉ F := by
      intro haf
      obtain ⟨x, hx⟩ := tupleSupport_nonempty hh a
      obtain ⟨j, rfl⟩ := mem_tupleSupport.mp hx
      exact ha_deleted j (Finset.mem_biUnion.mpr ⟨a, haf, hx⟩)
    have had : ∀ b ∈ F, Disjoint (tupleSupport a) (tupleSupport b) := by
      intro b hb
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      obtain ⟨j, rfl⟩ := mem_tupleSupport.mp hxa
      exact ha_deleted j (Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩)
    have hins : valid (insert a F) := by
      constructor
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hbad
        · exact hF.1 b hb
      · rw [Finset.coe_insert]
        exact Set.PairwiseDisjoint.insert_of_notMem hF.2 haF had
    have hle := hmax (insert a F) ((mem_candidates _).mpr hins)
    rw [Finset.card_insert_of_notMem haF] at hle
    exact Nat.not_succ_le_self F.card hle

end MetricEntropyDuality.DirectionDeletion

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.DirectionDeletion
open scoped Classical


theorem solution.{uU} : type_of% @_root_.OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset.{uU} := @_root_.OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset.{uU}
