-- Prove2me | solution 2 for OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:49:23.887173+00:00
-- url     : https://prove2.me/submissions/22b289e3-4498-402e-b08a-b80252f4409f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FiniteProductCounting.lean:L50-L85
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample. The node keeps its source
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

omit [Fintype U] [Fintype E] [DecidableEq E] in
theorem coordinateSwap_involutive (S : Finset U) :
    Function.Involutive (coordinateSwap (E := E) S) := by
  intro z
  apply Prod.ext <;> funext u <;> by_cases hu : u ∈ S <;> simp [coordinateSwap, hu]

/-- The two-event counting identity is a bijection of actual assignments. -/
theorem card_inter_mul_card_sample (S T : Finset U) (A B : Finset (U → E))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card (U → E) = A.card * B.card := by
  have hforward : ∀ z ∈ (A ∩ B).product (Finset.univ : Finset (U → E)),
      coordinateSwap S z ∈ A.product B := by
    rintro ⟨x, y⟩ hz
    have hxA := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).1
    have hxB := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).2
    apply Finset.mem_product.mpr
    constructor
    · apply (hA _ x ?_).mpr hxA
      intro u hu
      simp [coordinateSwap, hu]
    · apply (hB _ x ?_).mpr hxB
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [coordinateSwap, huS]
  have hreverse : ∀ z ∈ A.product B,
      coordinateSwap S z ∈ (A ∩ B).product (Finset.univ : Finset (U → E)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_inter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · apply (hA _ x ?_).mpr hx
      intro u hu
      simp [coordinateSwap, hu]
    · apply (hB _ y ?_).mpr hy
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [coordinateSwap, huS]
  have hc := Finset.card_nbij' (coordinateSwap S) (coordinateSwap S)
    hforward hreverse
    (fun z _ => coordinateSwap_involutive S z)
    (fun z _ => coordinateSwap_involutive S z)
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] using hc

section NonemptyAlphabet

variable [Nonempty E]

end NonemptyAlphabet

section FiniteIntersection

variable [Nonempty E]

end FiniteIntersection

end MetricEntropyDuality.FiniteProductCounting

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FiniteProductCounting
open scoped BigOperators


theorem solution.{uU,uE} : type_of% @_root_.OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample.{uU,uE} := @_root_.OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample.{uU,uE}
