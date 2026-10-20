-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_profile_pivots
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:58:49.010497+00:00
-- url     : https://prove2.me/submissions/3c287040-794f-4fee-bc03-2caa31e590c2

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

open OAI OAI.MetricEntropyDuality
universe uX uY uLabel
open scoped BigOperators Classical
theorem h51b_mono {X : Type*} {Y : Type*} [Nonempty X] [DecidableEq Y] (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) {k n : ℕ} (hk : k ≤ n) :
    GreedyPivots.covered μ I θ k ⊆ GreedyPivots.covered μ I θ n := by
  induction n, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    exact ih.trans (by
      show GreedyPivots.covered μ I θ m ⊆ GreedyPivots.covered μ I θ m ∪ _
      exact Finset.subset_union_left)

theorem h51b_gain {X : Type*} {Y : Type*} [Nonempty X] [DecidableEq Y] (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (k : ℕ)
    (hbad : ∃ x, θ < GreedyPivots.mass μ (I x \ GreedyPivots.covered μ I θ k)) :
    θ < GreedyPivots.mass μ (GreedyPivots.covered μ I θ (k + 1)) - GreedyPivots.mass μ (GreedyPivots.covered μ I θ k) := by
  have hp : θ < GreedyPivots.mass μ (I (GreedyPivots.choosePivot μ I θ (GreedyPivots.covered μ I θ k)) \ GreedyPivots.covered μ I θ k) := by
    unfold GreedyPivots.choosePivot
    rw [dif_pos hbad]
    exact hbad.choose_spec
  have : GreedyPivots.covered μ I θ (k + 1) = GreedyPivots.covered μ I θ k ∪
      (I (GreedyPivots.choosePivot μ I θ (GreedyPivots.covered μ I θ k)) \ GreedyPivots.covered μ I θ k) := by
    show _ ∪ _ = _
    rw [Finset.union_sdiff_self_eq_union]
  rw [this]
  unfold GreedyPivots.mass at hp ⊢
  rw [Finset.sum_union Finset.disjoint_sdiff]
  linarith

theorem h51b_bad {X : Type*} {Y : Type*} [Nonempty X] [DecidableEq Y] (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (n : ℕ) :
    (∃ x, θ < GreedyPivots.mass μ (I x \ GreedyPivots.covered μ I θ n)) →
      n = 0 ∨ (n : ℝ) * θ < GreedyPivots.mass μ (GreedyPivots.covered μ I θ n) := by
  rintro ⟨x, hx⟩
  have hgain : ∀ k, k < n → θ < GreedyPivots.mass μ (GreedyPivots.covered μ I θ (k + 1)) - GreedyPivots.mass μ (GreedyPivots.covered μ I θ k) := by
    intro k hk
    refine h51b_gain μ I θ k ⟨x, lt_of_lt_of_le hx ?_⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset_sdiff le_rfl (h51b_mono μ I θ hk.le)) (fun y _ _ => hμ y)
  have hz : GreedyPivots.mass μ (GreedyPivots.covered μ I θ 0) = 0 := by simp [GreedyPivots.mass]
  have key : ∀ m, m ≤ n → m = 0 ∨ (m : ℝ) * θ < GreedyPivots.mass μ (GreedyPivots.covered μ I θ m) := by
    intro m
    induction m with
    | zero => intro _; left; rfl
    | succ m ih =>
      intro hm
      right
      have g := hgain m (by omega)
      rcases ih (by omega) with h0 | h0
      · subst h0
        rw [hz] at g
        push_cast
        linarith
      · push_cast
        linarith
  exact key n le_rfl

theorem h51m_greedy {X : Type*} {Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (μ : Y → ℝ) (I : X → Finset Y) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) (θ : ℝ) (_hθ : 0 < θ) (s : ℕ)
    (hs : 1 ≤ (s : ℝ) * θ) :
    ∃ centers : Fin s → X, ∃ assigned : Y → Option (Fin s),
      (∀ y k, assigned y = some k → y ∈ I (centers k)) ∧
      (∀ y, (∃ k, y ∈ I (centers k)) ↔ assigned y ≠ none) ∧
      (∀ x, ∑ y ∈ (I x).filter (fun y => assigned y = none), μ y ≤ θ) := by
  classical
  let C := GreedyPivots.covered μ I θ
  let centers : Fin s → X := fun k => GreedyPivots.choosePivot μ I θ (C k)
  have hmem : ∀ n y, y ∈ C n ↔ ∃ k < n, y ∈ I (GreedyPivots.choosePivot μ I θ (C k)) := by
    intro n y
    induction n with
    | zero => simp [C]
    | succ n ih =>
      show y ∈ C n ∪ _ ↔ _
      rw [Finset.mem_union, ih]
      constructor
      · rintro (⟨k, hk, h⟩ | h)
        · exact ⟨k, by omega, h⟩
        · exact ⟨n, by omega, h⟩
      · rintro ⟨k, hk, h⟩
        rcases (by omega : k < n ∨ k = n) with h' | rfl
        · exact Or.inl ⟨k, h', h⟩
        · exact Or.inr h
  let assigned : Y → Option (Fin s) := fun y =>
    if h : ∃ k, y ∈ I (centers k) then some h.choose else none
  have hnone : ∀ y, assigned y = none ↔ ¬ ∃ k, y ∈ I (centers k) := by
    intro y
    simp only [assigned]
    split_ifs with h <;> simp [h]
  refine ⟨centers, assigned, ?_, ?_, ?_⟩
  · intro y k hk
    simp only [assigned] at hk
    split_ifs at hk with h
    · rw [Option.some.injEq] at hk
      rw [← hk]
      exact h.choose_spec
  · intro y
    rw [ne_eq, hnone, not_not]
  · intro x
    have heq : (I x).filter (fun y => assigned y = none) = I x \ C s := by
      ext y
      rw [Finset.mem_filter, Finset.mem_sdiff, hnone, hmem]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun ⟨k, hk, h⟩ => h2 ⟨⟨k, hk⟩, h⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun ⟨k, h⟩ => h2 ⟨k, k.2, h⟩⟩
    rw [heq]
    show GreedyPivots.mass μ (I x \ C s) ≤ θ
    by_contra hcon
    push_neg at hcon
    rcases h51b_bad μ I θ hμ s ⟨x, hcon⟩ with h0 | h0
    · subst h0
      simp at hs
      linarith
    · have : GreedyPivots.mass μ (C s) ≤ ∑ y, μ y :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => hμ y)
      linarith

theorem h51m_common {Y : Type*} [Fintype Y] {u : ℕ}
    (hu : 0 < u) (T : Y → Finset (Fin u)) (μ : Y → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ i : Fin u, (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ := by
  classical
  have hsum : ∑ i : Fin u, (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ ∑ _i : Fin u, θ := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    have : ∀ y, ∑ i : Fin u, (if i ∉ T y then μ y else 0) = ((Finset.univ \ T y).card : ℝ) * μ y := by
      intro y
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 2
      congr 1
      ext i; simp
    simp_rw [this]
    calc ∑ y, ((Finset.univ \ T y).card : ℝ) * μ y ≤ ∑ y, θ * (u : ℝ) * μ y :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_right (hcomp y) (hμ y))
      _ = θ * u * ∑ y, μ y := by rw [Finset.mul_sum]
      _ ≤ θ * u * 1 := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = ∑ _i : Fin u, θ := by simp; ring
  have hne : (Finset.univ : Finset (Fin u)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hu⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨i, hi⟩

theorem solution {X : Type uX} {Y : Type uY}
    [Fintype X] [Nonempty X] [Fintype Y]
    {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (v : Y → X) (T : Y → Finset (Fin u))
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (θ : ℝ) (hθ : 0 < θ) (s : ℕ) (hs : 1 ≤ (s : ℝ) * θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) (h : ℕ) :
    ∃ i : Fin u, ∃ centers : Fin h → Fin s → X,
      ∃ assigned : Fin h → Y → Option (Fin s),
        (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ ∧
        (∀ j y k, assigned j y = some k →
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val (centers j k) (v y)) ∧
        (∀ j x, (∑ y ∈ Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y) ∧
            assigned j y = none), μ y) ≤ θ) := by
  classical
  obtain ⟨i, hi⟩ := h51m_common hu T μ hμ hmass hθ.le hcomp
  have hg : ∀ j : Fin h, ∃ centers : Fin s → X, ∃ assigned : Y → Option (Fin s),
      (∀ y k, assigned y = some k → y ∈ (Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val (centers k) (v y)))) ∧
      (∀ x, ∑ y ∈ (Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y))).filter (fun y => assigned y = none), μ y ≤ θ) := by
    intro j
    obtain ⟨c, a, h1, -, h3⟩ := h51m_greedy μ (fun x => Finset.univ.filter (fun y =>
      i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y))) hμ hmass θ hθ s hs
    exact ⟨c, a, h1, h3⟩
  choose centers assigned hA hB using hg
  refine ⟨i, centers, assigned, hi, ?_, ?_⟩
  · intro j y k hk
    have := hA j y k hk
    simpa using this
  · intro j x
    have := hB j x
    rw [Finset.filter_filter] at this
    convert this using 2
    ext y; simp [and_assoc]

