-- Prove2me | solution 1 for OAI.MetricEntropyDuality.FiniteProductCounting.card_inter_mul_card_sample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:34:51.18651+00:00
-- url     : https://prove2.me/submissions/0e8736ab-7863-44fa-95ff-21811a6259c6

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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FiniteProductCounting
universe uU uE uJ
open scoped BigOperators
variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]


theorem solution (S T : Finset U) (A B : Finset (U → E))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card (U → E) = A.card * B.card := by
  have hinv : ∀ z : (U → E) × (U → E), coordinateSwap S (coordinateSwap S z) = z := by
    intro z; ext u <;> simp only [coordinateSwap] <;> split_ifs <;> rfl
  have hT : ∀ u ∈ T, u ∉ S := fun u hu hs => Finset.disjoint_left.mp hST hs hu
  rw [← Finset.card_univ, ← Finset.card_product, ← Finset.card_product]
  apply Finset.card_nbij' (coordinateSwap S) (coordinateSwap S)
  · rintro ⟨ω, η⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_inter] at h ⊢
    obtain ⟨⟨hA1, hB1⟩, -⟩ := h
    constructor
    · exact (hA _ ω (fun u hu => by simp [coordinateSwap, hu])).mpr hA1
    · exact (hB _ ω (fun u hu => by simp [coordinateSwap, hT u hu])).mpr hB1
  · rintro ⟨a, b⟩ h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_inter,
      Finset.mem_univ, and_true] at h ⊢
    obtain ⟨ha, hb⟩ := h
    constructor
    · exact (hA _ a (fun u hu => by simp [coordinateSwap, hu])).mpr ha
    · exact (hB _ b (fun u hu => by simp [coordinateSwap, hT u hu])).mpr hb
  · intro z _; exact hinv z
  · intro z _; exact hinv z

