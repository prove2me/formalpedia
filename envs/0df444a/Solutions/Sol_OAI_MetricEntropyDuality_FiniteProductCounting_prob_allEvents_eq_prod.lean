-- Prove2me | solution 1 for OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:36:50.84159+00:00
-- url     : https://prove2.me/submissions/6e15e67c-1980-4f88-9434-e2ca2465d42d

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
variable [Nonempty E]
theorem h51a_pair {U : Type*} {E : Type*} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]
    (S T : Finset U) (A B : Finset (U → E))
    (hA : OAI.MetricEntropyDuality.FiniteProductCounting.DependsOn S A)
    (hB : OAI.MetricEntropyDuality.FiniteProductCounting.DependsOn T B) (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card (U → E) = A.card * B.card := by
  have h : ((A ∩ B) ×ˢ (Finset.univ : Finset (U → E))).card = (A ×ˢ B).card := by
    refine Finset.card_nbij' (OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap S)
      (OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap S) ?_ ?_ ?_ ?_
    · rintro ⟨ω, η⟩ hz
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_inter,
        Finset.mem_univ, and_true] at hz ⊢
      simp only [OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap]
      refine ⟨(hA _ ω (fun u hu => by simp [hu])).mpr hz.1, (hB _ ω (fun u hu => ?_)).mpr hz.2⟩
      have : u ∉ S := Finset.disjoint_right.mp hST hu
      simp [this]
    · rintro ⟨ω, η⟩ hz
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_inter,
        Finset.mem_univ, and_true] at hz ⊢
      simp only [OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap]
      refine ⟨(hA _ ω (fun u hu => by simp [hu])).mpr hz.1, (hB _ η (fun u hu => ?_)).mpr hz.2⟩
      have : u ∉ S := Finset.disjoint_right.mp hST hu
      simp [this]
    · rintro ⟨ω, η⟩ _
      simp only [OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap, Prod.mk.injEq]
      constructor <;> funext u <;> by_cases hu : u ∈ S <;> simp [hu]
    · rintro ⟨ω, η⟩ _
      simp only [OAI.MetricEntropyDuality.FiniteProductCounting.coordinateSwap, Prod.mk.injEq]
      constructor <;> funext u <;> by_cases hu : u ∈ S <;> simp [hu]
  rw [Finset.card_product, Finset.card_product, Finset.card_univ] at h
  exact h

theorem solution {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    prob (allEvents s A) = ∏ j ∈ s, prob (A j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hdep' : ∀ i ∈ s, DependsOn (S i) (A i) := fun i hi => hdep i (Finset.mem_insert_of_mem hi)
    have hdisj' : ∀ i ∈ s, ∀ k ∈ s, i ≠ k → Disjoint (S i) (S k) := fun i hi k hk =>
      hdisj i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hj, ← ih hdep' hdisj']
    have hEdep : DependsOn (s.biUnion S) (allEvents s A) := by
      intro ω η hag
      simp only [mem_allEvents]
      constructor
      · intro h i hi
        exact (hdep' i hi ω η (fun u hu => hag u (Finset.mem_biUnion.mpr ⟨i, hi, hu⟩))).mp (h i hi)
      · intro h i hi
        exact (hdep' i hi ω η (fun u hu => hag u (Finset.mem_biUnion.mpr ⟨i, hi, hu⟩))).mpr (h i hi)
    have hD : Disjoint (S j) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj j (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => hj (e ▸ hi))
    have hset : allEvents (insert j s) A = A j ∩ allEvents s A := by
      ext ω
      simp [Finset.mem_insert]
    have key := h51a_pair (S j) (s.biUnion S) (A j) (allEvents s A)
      (hdep j (Finset.mem_insert_self _ _)) hEdep hD
    have hN := sample_card_pos (U := U) (E := E)
    rw [hset]
    unfold prob
    have hc : (((A j ∩ allEvents s A).card : ℕ) : ℝ) =
        ((A j).card : ℝ) * ((allEvents s A).card : ℝ) / (Fintype.card (U → E) : ℝ) := by
      rw [eq_div_iff hN.ne']
      exact_mod_cast key
    rw [hc]
    field_simp

