-- Prove2me | solution 2 for OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:50:33.053613+00:00
-- url     : https://prove2.me/submissions/5081ef7d-26a3-4c2f-8c7c-6b5f8ace444d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FiniteProductCounting.lean:L158-L179
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_FiniteProductCounting_card_inter_mul_card_sample

-- ---- from OAI.Analysis.MetricEntropy.FiniteProductCounting ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uU uE uJ

/-!
# Counting events on disjoint sets of coordinates

The sample space is the actual finite function space `U → E`, with uniform
probability given by cardinality divided by the cardinality of that space.
A coordinate-swap bijection proves independence of two events from their
literal disjoint supports. Finite intersections then follow by induction.
No independence hypothesis or distinctness within an individual tuple is used.
-/

namespace MetricEntropyDuality.FiniteProductCounting

open scoped BigOperators

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]

section NonemptyAlphabet

variable [Nonempty E]

/-- Uniform independence is derived from disjoint coordinate supports. -/
theorem prob_inter (S T : Finset U) (A B : Finset (U → E))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    prob (A ∩ B) = prob A * prob B := by
  have hN : (Fintype.card (U → E) : ℝ) ≠ 0 := ne_of_gt sample_card_pos
  have hcard : ((A ∩ B).card : ℝ) * (Fintype.card (U → E) : ℝ) =
      (A.card : ℝ) * (B.card : ℝ) := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ))
      (card_inter_mul_card_sample S T A B hA hB hST)
  unfold prob
  apply (div_eq_iff hN).mpr
  rw [mul_assoc, div_mul_cancel₀ _ hN, div_mul_eq_mul_div]
  exact (eq_div_iff hN).mpr hcard

end NonemptyAlphabet

theorem allEvents_insert {J : Type uJ} [DecidableEq J]
    (j : J) (s : Finset J) (A : J → Finset (U → E)) :
    allEvents (insert j s) A = A j ∩ allEvents s A := by
  ext ω
  simp

theorem dependsOn_allEvents {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j)) :
    DependsOn (s.biUnion S) (allEvents s A) := by
  intro ω η hagree
  simp only [mem_allEvents]
  have hiff (j : J) (hj : j ∈ s) : ω ∈ A j ↔ η ∈ A j :=
    hdep j hj ω η (fun u hu => hagree u (Finset.mem_biUnion.mpr ⟨j, hj, hu⟩))
  constructor
  · intro h j hj
    exact (hiff j hj).mp (h j hj)
  · intro h j hj
    exact (hiff j hj).mpr (h j hj)

section FiniteIntersection

variable [Nonempty E]

/-- Every finite family of events on pairwise disjoint supports factors. -/
theorem prob_allEvents_eq_prod {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    prob (allEvents s A) = ∏ j ∈ s, prob (A j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hdepS : ∀ j ∈ s, DependsOn (S j) (A j) :=
        fun j hj => hdep j (Finset.mem_insert_of_mem hj)
      have hdisjS : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → Disjoint (S j) (S l) :=
        fun j hj l hl => hdisj j (Finset.mem_insert_of_mem hj)
          l (Finset.mem_insert_of_mem hl)
      have hdisjI : Disjoint (S i) (s.biUnion S) := by
        apply (Finset.disjoint_biUnion_right (S i) s S).mpr
        intro j hj
        exact hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun hij => hi (hij.symm ▸ hj))
      rw [allEvents_insert, prob_inter (S i) (s.biUnion S) (A i) (allEvents s A)
        (hdep i (Finset.mem_insert_self _ _)) (dependsOn_allEvents s S A hdepS) hdisjI,
        ih hdepS hdisjS, Finset.prod_insert hi]

end FiniteIntersection

end MetricEntropyDuality.FiniteProductCounting

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FiniteProductCounting
open scoped BigOperators


theorem solution.{uU,uE,uJ} : type_of% @_root_.OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod.{uU,uE,uJ} := @_root_.OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod.{uU,uE,uJ}
