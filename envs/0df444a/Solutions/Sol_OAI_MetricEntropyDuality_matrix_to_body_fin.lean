-- Prove2me | solution 1 for OAI.MetricEntropyDuality.matrix_to_body_fin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:40:28.886878+00:00
-- url     : https://prove2.me/submissions/8563e2f8-0475-412b-baf0-32e0d8c28775

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

open OAI OAI.MetricEntropyDuality
universe uX uY uι
open scoped Pointwise
variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]
theorem h51a_cube_eq {α : Type*} : cube α = Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

theorem h51a_cube_body {α : Type*} [Fintype α] : IsSymmetricConvexBody (cube α) := by
  refine IsSymmetricConvexBody.mk ?_ ?_ ?_ ?_
  · rw [h51a_cube_eq]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  · rw [h51a_cube_eq]
    exact convex_pi (fun _ _ => convex_Icc _ _)
  · intro x
    simp [cube, abs_neg]
  · refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : RealSpace α) one_pos) ?_
    intro z hz i
    have := (dist_le_pi_dist z 0 i).trans_lt hz
    rw [Real.dist_eq] at this
    simp only [Pi.zero_apply, sub_zero] at this
    exact this.le

theorem h51a_memK {α : Type*} (S T : Set (α → ℝ)) (c d : ℝ) (z : α → ℝ) :
    z ∈ c • S + d • T ↔ ∃ h ∈ S, ∃ q ∈ T, c • h + d • q = z := by
  simp only [Set.mem_add, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨h, hh, q, hq, rfl⟩
  · rintro ⟨h, hh, q, hq, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩

theorem h51a_hull_neg {α β : Type*} (g : β → α → ℝ) (z : RealSpace β)
    (hz : z ∈ absRowHull g) : -z ∈ absRowHull g := by
  have hS : -(Set.range (row g) ∪ Set.range (fun x => -row g x)) =
      (Set.range (row g) ∪ Set.range (fun x => -row g x)) := by
    ext w
    simp only [Set.mem_neg, Set.mem_union, Set.mem_range]
    constructor
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact Or.inr ⟨x, by rw [hx, neg_neg]⟩
      · exact Or.inl ⟨x, by rw [← neg_neg (row g x), hx, neg_neg]⟩
    · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
      · exact Or.inr ⟨x, by rw [hx]⟩
      · exact Or.inl ⟨x, by rw [← hx, neg_neg]⟩
  have : absRowHull g = -absRowHull g := by
    unfold absRowHull
    rw [← convexHull_neg, hS]
  rw [this] at hz
  exact hz

theorem h51a_zero_hull {α β : Type*} [Nonempty α] (g : β → α → ℝ) :
    (0 : RealSpace β) ∈ absRowHull g := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have h1 : row g x ∈ absRowHull g := subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩)
  have h2 : -row g x ∈ absRowHull g := subset_convexHull ℝ _ (Or.inr ⟨x, rfl⟩)
  have := convex_convexHull ℝ _ h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  rw [smul_neg, add_neg_cancel] at this
  exact this

theorem h51a_body {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] (g : β → α → ℝ)
    {t : ℝ} (ht : 0 < t) :
    IsSymmetricConvexBody ((3 : ℝ) • absRowHull g + t • cube β) := by
  have hHc : IsCompact (absRowHull g) := by
    apply Set.Finite.isCompact_convexHull
    exact (Set.finite_range _).union (Set.finite_range _)
  have hsymm : ∀ x, x ∈ (3 : ℝ) • absRowHull g + t • cube β → -x ∈ (3 : ℝ) • absRowHull g + t • cube β := by
    intro x hx
    rw [h51a_memK] at hx ⊢
    obtain ⟨h, hh, q, hq, rfl⟩ := hx
    refine ⟨-h, h51a_hull_neg g h hh, -q, (h51a_cube_body.symmetric q).mp hq, ?_⟩
    simp [smul_neg]; abel
  refine IsSymmetricConvexBody.mk ?_ ?_ ?_ ?_
  · exact (hHc.smul (3 : ℝ)).add (h51a_cube_body.isCompact.smul t)
  · exact ((convex_convexHull ℝ _).smul 3).add (h51a_cube_body.convex.smul t)
  · intro x
    exact ⟨hsymm x, fun h => by simpa using hsymm (-x) h⟩
  · refine ⟨0, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : RealSpace β) ht) ?_
    intro z hz
    rw [h51a_memK]
    refine ⟨0, h51a_zero_hull g, t⁻¹ • z, ?_, ?_⟩
    · intro i
      have := (dist_le_pi_dist z 0 i).trans_lt hz
      rw [Real.dist_eq] at this
      simp only [Pi.zero_apply, sub_zero] at this
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos ht]
      rw [inv_mul_le_iff₀ ht, mul_one]
      exact this.le
    · simp [smul_smul, ht.ne']

theorem h51a_coverable_of_compact {α : Type*} [Fintype α] (K : Set (RealSpace α))
    (hK : IsCompact K) : Coverable K (cube α) := by
  obtain ⟨s, -, hs, hcov⟩ := finite_cover_balls_of_compact hK one_pos
  refine ⟨hs.toFinset.card, fun j => (hs.toFinset.equivFin.symm j : RealSpace α), ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
  refine ⟨hs.toFinset.equivFin ⟨c, hs.mem_toFinset.mpr hc⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  intro i
  have := (dist_le_pi_dist x c i).trans_lt (Metric.mem_ball.mp hxc)
  rw [Real.dist_eq] at this
  simpa using this.le

theorem h51a_card_le {α β : Type*} [Fintype α] [Fintype β] (g : β → α → ℝ)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (K : Set (RealSpace β)) (hK : ∀ x, (3 : ℝ) • row g x ∈ K)
    (hcov : Coverable K (cube β)) : Fintype.card α ≤ coveringNumber K (cube β) := by
  have hne : {M | ∃ centers : Fin M → RealSpace β, Covers K (cube β) centers}.Nonempty := hcov
  obtain ⟨centers, hc⟩ := Nat.sInf_mem hne
  unfold coveringNumber
  choose f hf using fun x => hc _ (hK x)
  have hinj : Function.Injective f := by
    intro x x' hxx
    by_contra hne'
    obtain ⟨y, hy⟩ := hsep x x' hne'
    have h1 := hf x
    have h2 := hf x'
    simp only [cube, Set.mem_setOf_eq] at h1 h2
    have h1y := h1 y
    have h2y := h2 y
    rw [hxx] at h1y
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, row] at h1y h2y
    have : |g y x - g y x'| ≤ 2 / 3 := by
      rw [abs_le] at h1y h2y ⊢
      constructor <;> linarith [h1y.1, h1y.2, h2y.1, h2y.2]
    linarith
  simpa using Fintype.card_le_of_injective f hinj

theorem h51a_pairing_le_l1 {α : Type*} [Fintype α] (q δ : RealSpace α) (hq : q ∈ cube α) :
    pairing q δ ≤ l1Norm δ := by
  unfold pairing l1Norm
  refine Finset.sum_le_sum fun i _ => ?_
  calc q i * δ i ≤ |q i * δ i| := le_abs_self _
    _ = |q i| * |δ i| := abs_mul _ _
    _ ≤ |δ i| := mul_le_of_le_one_left (abs_nonneg _) (hq i)

theorem h51a_polar_cube {α : Type*} [Fintype α] (δ : RealSpace α) (hδ : δ ∈ polar (cube α)) :
    δ ∈ l1Ball α := by
  have hx : (fun i => if 0 ≤ δ i then (1:ℝ) else -1) ∈ cube α := by
    intro i
    dsimp only
    split_ifs <;> simp
  have := (show ∀ x ∈ cube α, pairing x δ ≤ 1 from hδ) _ hx
  show l1Norm δ ≤ 1
  convert this using 1
  unfold pairing l1Norm
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.mp h)]

theorem h51a_mem_smul_polar {ι : Type*} [Fintype ι] (K : Set (RealSpace ι)) (δ : RealSpace ι)
    {c : ℝ} (hc : 0 < c) : δ ∈ c • polar K ↔ ∀ z ∈ K, pairing z δ ≤ c := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [polar, Set.mem_setOf_eq]
  have hp : ∀ z, pairing z (c⁻¹ • δ) = c⁻¹ * pairing z δ := by
    intro z
    simp [pairing, Finset.mul_sum, mul_left_comm]
  simp_rw [hp, inv_mul_le_iff₀ hc, mul_one]

theorem h51a_coeff_reps {α β : Type*} [Fintype β] (g : β → α → ℝ) (ε : ℝ)
    (A : Finset (RealSpace α)) (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace β,
      (∀ j, centers j ∈ l1Ball β) ∧
      ∀ lam ∈ l1Ball β, ∃ j,
        UniformClose (2 * ε) (columnCombination g lam) (columnCombination g (centers j)) ∧
        l1Norm (lam - centers j) ≤ 2 := by
  classical
  let rep : RealSpace α → RealSpace β := fun a =>
    if h : ∃ lam ∈ l1Ball β, UniformClose ε (columnCombination g lam) a then h.choose else 0
  have hrep_mem : ∀ a, rep a ∈ l1Ball β := by
    intro a
    simp only [rep]
    split_ifs with h
    · exact h.choose_spec.1
    · exact zero_mem_l1Ball
  refine ⟨fun j => rep (A.equivFin.symm j), fun j => hrep_mem _, ?_⟩
  intro lam hlam
  obtain ⟨a, haA, hla⟩ := hA lam hlam
  have hex : ∃ lam ∈ l1Ball β, UniformClose ε (columnCombination g lam) a := ⟨lam, hlam, hla⟩
  have hra : rep a = hex.choose := by simp only [rep, dif_pos hex]
  refine ⟨A.equivFin ⟨a, haA⟩, ?_, ?_⟩
  · simp only [Equiv.symm_apply_apply]
    rw [hra]
    have h2 := hex.choose_spec.2
    intro x
    have e1 := hla x
    have e2 := h2 x
    calc |columnCombination g lam x - columnCombination g hex.choose x|
        = |(columnCombination g lam x - a x) - (columnCombination g hex.choose x - a x)| := by
          congr 1; ring
      _ ≤ |columnCombination g lam x - a x| + |columnCombination g hex.choose x - a x| :=
          abs_sub _ _
      _ ≤ 2 * ε := by linarith
  · simp only [Equiv.symm_apply_apply]
    have hm := hrep_mem a
    simp only [l1Ball, l1Norm, Set.mem_setOf_eq] at hm hlam ⊢
    calc ∑ i, |(lam - rep a) i| ≤ ∑ i, (|lam i| + |rep a i|) :=
          Finset.sum_le_sum (fun i _ => by simpa using abs_sub (lam i) (rep a i))
      _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith

theorem h51a_main {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (g : β → α → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace α)) (hA : UniformApproximation g ε A) :
    ∃ K : Set (RealSpace β),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube β) ∧
        Coverable K (cube β) ∧
        Coverable (polar (cube β)) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card α ≤ coveringNumber K (cube β) ∧
        coveringNumber (polar (cube β)) ((6 * ε + 2 * t) • polar K) ≤ A.card := by
  have hK := h51a_body g (β := β) ht
  have hKcov := h51a_coverable_of_compact _ hK.isCompact
  obtain ⟨centers, -, hcen⟩ := h51a_coeff_reps g ε A hA
  have hc : 0 < 6 * ε + 2 * t := by linarith
  have hlin : IsLinearMap ℝ (fun h : RealSpace β => pairing h (0 : RealSpace β)) := by
    constructor <;> intros <;> simp
  have hdual : Covers (polar (cube β)) ((6 * ε + 2 * t) •
      polar ((3 : ℝ) • absRowHull g + t • cube β)) centers := by
    intro lam hlam
    obtain ⟨j, hj1, hj2⟩ := hcen lam (h51a_polar_cube lam hlam)
    refine ⟨j, ?_⟩
    rw [h51a_mem_smul_polar _ _ hc]
    intro z hz
    rw [h51a_memK] at hz
    obtain ⟨h, hh, q, hq, rfl⟩ := hz
    set δ := lam - centers j with hδ
    have hpl : IsLinearMap ℝ (fun w : RealSpace β => pairing w δ) := by
      constructor
      · intro x y
        simp [pairing, add_mul, Finset.sum_add_distrib]
      · intro c x
        simp [pairing, Finset.mul_sum, mul_assoc]
    have hrow : ∀ x, pairing (row g x) δ =
        columnCombination g lam x - columnCombination g (centers j) x := by
      intro x
      simp only [pairing, row, columnCombination, hδ, Pi.sub_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hH : pairing h δ ≤ 2 * ε := by
      have hsub : absRowHull g ⊆ {w | pairing w δ ≤ 2 * ε} := by
        apply convexHull_min _ (convex_halfSpace_le hpl _)
        rintro w (⟨x, rfl⟩ | ⟨x, rfl⟩)
        · show pairing (row g x) δ ≤ 2 * ε
          rw [hrow]
          exact (le_abs_self _).trans (hj1 x)
        · show pairing (-row g x) δ ≤ 2 * ε
          rw [pairing_neg_left, hrow]
          exact (neg_le_abs _).trans (hj1 x)
      exact hsub hh
    have hQ : pairing q δ ≤ 2 := (h51a_pairing_le_l1 q δ hq).trans hj2
    have hsplit : pairing ((3:ℝ) • h + t • q) δ = 3 * pairing h δ + t * pairing q δ := by
      simp [pairing, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [hsplit]
    nlinarith
  refine ⟨_, hK, h51a_cube_body, hKcov, ⟨_, centers, hdual⟩, ?_, Nat.sInf_le ⟨centers, hdual⟩⟩
  refine h51a_card_le g hsep _ (fun x => ?_) hKcov
  rw [h51a_memK]
  exact ⟨row g x, subset_convexHull ℝ _ (Or.inl ⟨x, rfl⟩), 0, zero_mem_cube, by simp⟩

theorem h51a_transfer {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (g : β → α → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace α)) (hA : UniformApproximation g ε A) :
    ∃ K : Set (RealSpace (Fin (Fintype.card β))),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube (Fin (Fintype.card β))) ∧
        Coverable K (cube (Fin (Fintype.card β))) ∧
        Coverable (polar (cube (Fin (Fintype.card β)))) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card α ≤ coveringNumber K (cube (Fin (Fintype.card β))) ∧
        coveringNumber (polar (cube (Fin (Fintype.card β))))
          ((6 * ε + 2 * t) • polar K) ≤ A.card := by
  let e := Fintype.equivFin β
  let g' : Fin (Fintype.card β) → α → ℝ := fun y' x => g (e.symm y') x
  apply h51a_main g' hε ht
  · intro x x' hx
    obtain ⟨y, hy⟩ := hsep x x' hx
    exact ⟨e y, by simpa [g'] using hy⟩
  · intro lam' hlam'
    let lam : RealSpace β := fun y => lam' (e y)
    have hl : lam ∈ l1Ball β := by
      have : l1Norm lam = l1Norm lam' := by
        unfold l1Norm
        exact Equiv.sum_comp e (fun i => |lam' i|)
      show l1Norm lam ≤ 1
      rw [this]
      exact hlam'
    obtain ⟨a, ha, hcl⟩ := hA lam hl
    refine ⟨a, ha, ?_⟩
    have : columnCombination g' lam' = columnCombination g lam := by
      funext x
      unfold columnCombination
      rw [← Equiv.sum_comp e]
      simp [g', lam]
    rw [this]
    exact hcl

theorem solution [Nonempty X] [Nonempty Y]
    (g : Y → X → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    0 < Fintype.card Y ∧
      ∃ K : Set (RealSpace (Fin (Fintype.card Y))),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube (Fin (Fintype.card Y))) ∧
        Coverable K (cube (Fin (Fintype.card Y))) ∧
        Coverable (polar (cube (Fin (Fintype.card Y)))) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card X ≤ coveringNumber K (cube (Fin (Fintype.card Y))) ∧
        coveringNumber (polar (cube (Fin (Fintype.card Y))))
          ((6 * ε + 2 * t) • polar K) ≤ A.card := by
  exact ⟨Fintype.card_pos, h51a_transfer g hε ht hsep A hA⟩

