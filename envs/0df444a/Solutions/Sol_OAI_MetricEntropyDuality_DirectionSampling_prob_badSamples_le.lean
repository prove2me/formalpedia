-- Prove2me | solution 1 for OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:36:14.017116+00:00
-- url     : https://prove2.me/submissions/c316cd32-3767-4394-a085-f92b19614688

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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.DirectionSampling
universe uU uE uJ uZ
open scoped BigOperators
open FiniteProductCounting
variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}
section h51ds
variable {U' : Type*} {E' : Type*} [Fintype U'] [DecidableEq U'] [Fintype E'] [DecidableEq E']

lemma h51m_card_inter (S T : Finset U') (A B : Finset (U' → E'))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card (U' → E') = A.card * B.card := by
  have hinv : ∀ z : (U' → E') × (U' → E'), coordinateSwap S (coordinateSwap S z) = z := by
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

lemma h51m_prob_inter (S T : Finset U') (A B : Finset (U' → E'))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    prob (A ∩ B) = prob A * prob B := by
  have := h51m_card_inter S T A B hA hB hST
  unfold prob
  rcases Nat.eq_zero_or_pos (Fintype.card (U' → E')) with h0 | hpos
  · simp [h0]
  · have hN : (Fintype.card (U' → E') : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have : ((A ∩ B).card : ℝ) * Fintype.card (U' → E') = A.card * B.card := by exact_mod_cast this
    field_simp
    linarith

lemma h51m_prod [Nonempty E'] {J : Type*} [DecidableEq J] (s : Finset J) (S : J → Finset U') (A : J → Finset (U' → E'))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    prob (allEvents s A) = ∏ j ∈ s, prob (A j) := by
  induction s using Finset.induction_on with
  | empty =>
    have : allEvents (∅ : Finset J) A = Finset.univ := by ext; simp
    rw [this, Finset.prod_empty]
    unfold prob; rw [Finset.card_univ]
    rcases Nat.eq_zero_or_pos (Fintype.card (U' → E')) with h0 | hpos
    · exfalso; exact (Fintype.card_pos (α := U' → E')).ne' h0
    · have : (Fintype.card (U' → E') : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
  | @insert j s hj ih =>
    have hsplit : allEvents (insert j s) A = A j ∩ allEvents s A := by
      ext ω; simp
    have hdep' : DependsOn (s.biUnion S) (allEvents s A) := by
      intro ω η hωη
      simp only [mem_allEvents]
      constructor
      · intro h i hi
        exact (hdep i (Finset.mem_insert_of_mem hi) ω η (fun u hu =>
          hωη u (Finset.mem_biUnion.mpr ⟨i, hi, hu⟩))).mp (h i hi)
      · intro h i hi
        exact (hdep i (Finset.mem_insert_of_mem hi) ω η (fun u hu =>
          hωη u (Finset.mem_biUnion.mpr ⟨i, hi, hu⟩))).mpr (h i hi)
    have hd : Disjoint (S j) (s.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj j (Finset.mem_insert_self j s) i (Finset.mem_insert_of_mem hi)
        (fun h => hj (h ▸ hi))
    rw [hsplit, h51m_prob_inter (S j) (s.biUnion S) _ _ (hdep j (Finset.mem_insert_self j s)) hdep' hd,
      Finset.prod_insert hj, ih (fun i hi => hdep i (Finset.mem_insert_of_mem hi))
        (fun a ha b hb => hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))]

lemma h51m_prob_union {α : Type*} (X : Finset α) (f : α → Finset (U' → E')) :
    prob (X.biUnion f) ≤ ∑ x ∈ X, prob (f x) := by
  unfold prob
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_biUnion_le

end h51ds

theorem solution (forms : Finset Z) (bad : Z → (Fin h → E) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u, prob (tupleEvent (bad z) a) ≤ b) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (forms.card : ℝ) * (u : ℝ) ^ (h * w) * b ^ w := by
  classical
  have hlist : ∀ z ∈ forms, ∀ L ∈ disjointLists u h w, prob (badListEvent (E := E) (bad z) L) ≤ b ^ w := by
    intro z hz L hL
    rw [mem_disjointLists] at hL
    unfold badListEvent
    rw [h51m_prod Finset.univ (fun j => tupleSupport (L j)) (fun j => tupleEvent (bad z) (L j))]
    · calc ∏ j, prob (tupleEvent (bad z) (L j)) ≤ ∏ _j : Fin w, b :=
            Finset.prod_le_prod (fun j _ => by unfold prob; positivity) (fun j _ => hbound z hz (L j))
        _ = b ^ w := by simp
    · intro j _ ω η hωη
      simp only [mem_tupleEvent]
      have : (fun i => ω (L j i)) = (fun i => η (L j i)) := by
        funext i; exact hωη _ (mem_tupleSupport.mpr ⟨i, rfl⟩)
      rw [this]
    · intro i _ j _ hij
      exact hL hij
  have hcard : ((disjointLists u h w).card : ℝ) ≤ (u : ℝ) ^ (h * w) := by
    have : (disjointLists u h w).card ≤ u ^ (h * w) := by
      calc (disjointLists u h w).card ≤ (Finset.univ : Finset (Fin w → Fin h → Fin u)).card :=
            Finset.card_le_univ _
        _ = u ^ (h * w) := by
            rw [Finset.card_univ]; simp [Fintype.card_fun, ← pow_mul, mul_comm]
    exact_mod_cast this
  unfold badSamples
  calc prob (forms.biUnion fun z => (disjointLists u h w).biUnion fun L => badListEvent (bad z) L)
      ≤ ∑ z ∈ forms, prob ((disjointLists u h w).biUnion fun L => badListEvent (bad z) L) :=
        h51m_prob_union _ _
    _ ≤ ∑ z ∈ forms, ∑ L ∈ disjointLists u h w, prob (badListEvent (E := E) (bad z) L) :=
        Finset.sum_le_sum (fun z _ => h51m_prob_union _ _)
    _ ≤ ∑ z ∈ forms, ∑ L ∈ disjointLists u h w, b ^ w :=
        Finset.sum_le_sum (fun z hz => Finset.sum_le_sum (fun L hL => hlist z hz L hL))
    _ = (forms.card : ℝ) * ((disjointLists u h w).card * b ^ w) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (forms.card : ℝ) * ((u : ℝ) ^ (h * w) * b ^ w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

