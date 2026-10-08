-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.monotone_implementable
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T06:00:35.962635+00:00
-- url     : https://prove2.me/submissions/9f60f837-4742-40d8-b3b3-c465bcd2979e

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false

set_option autoImplicit false

namespace RochetFinitePricing
open MechanismDesign.IncentiveCompat
variable {A Θ : Type*}

/-- With nontrivial one-dimensional types, indifferent outcomes have equal
utility at every type. This preserves preorder ties in finite pricing. -/
theorem utility_eq_of_indiff [Nontrivial Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (h1 : OneDimensional u R) {a b : A}
    (hab : Indiff R a b) (θ : Θ) : u a θ = u b θ := by
  obtain ⟨η,hη⟩ := exists_ne θ
  rcases h1 θ η hη.symm with hθη | hηθ
  · obtain ⟨heq,hzero⟩ := hθη.2 a b hab
    apply sub_eq_zero.mp
    exact heq.trans hzero
  · exact sub_eq_zero.mp (hηθ.2 a b hab).2

theorem implementable_of_constant (u : A → Θ → ℝ) (q : Θ → A)
    (hq : ∀ x y : Θ, q x = q y) : Implementable u q := by
  refine ⟨fun _ => 0, ?_⟩
  intro x y
  change u (q y) x - 0 ≤ u (q x) x - 0
  rw [hq y x]

/-- A strict allocation order forces the same higher-type orientation. -/
theorem higher_of_strict_alloc (u : A → Θ → ℝ) (R : A → A → Prop)
    (h1 : OneDimensional u R) (q : Θ → A) (hq : MonotoneWRT u R q)
    {x y : Θ} (halloc : StrictPart R (q x) (q y)) : HigherType u R x y := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact halloc.2 halloc.1
  rcases h1 x y hne with hxy | hyx
  · exact hxy
  · exact False.elim (halloc.2 (hq y x hyx))

theorem strict_margin_of_strict_alloc (u : A → Θ → ℝ) (R : A → A → Prop)
    (h1 : OneDimensional u R) (q : Θ → A) (hq : MonotoneWRT u R q)
    {x y : Θ} (halloc : StrictPart R (q x) (q y)) {a b : A}
    (hab : StrictPart R a b) : u a y - u b y < u a x - u b x :=
  (higher_of_strict_alloc u R h1 q hq halloc).1 a b hab

/-- A bounded family of high-allocation margins has an infimum separating
all lower-allocation margins, even when no type attains the infimum. -/
theorem exists_separating_price (u : A → Θ → ℝ) (R : A → A → Prop)
    (hbdd : IsBoundedTypeSpace u) (h1 : OneDimensional u R)
    (q : Θ → A) (hq : MonotoneWRT u R q)
    (H L : Set Θ) (hH : H.Nonempty)
    (hsep : ∀ x ∈ H, ∀ y ∈ L, StrictPart R (q x) (q y))
    {a b : A} (hab : StrictPart R a b) :
    ∃ price : ℝ, (∀ y ∈ L, u a y - u b y ≤ price) ∧
      (∀ x ∈ H, price ≤ u a x - u b x) := by
  let S : Set ℝ := (fun x => u a x - u b x) '' H
  have hSne : S.Nonempty := hH.image _
  obtain ⟨c, hc, hbounds⟩ := hbdd
  have hbelow : BddBelow S := by
    refine ⟨-c, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact (hbounds b a x).1.le
  refine ⟨sInf S, ?_, ?_⟩
  · intro y hy
    apply le_csInf hSne
    rintro z ⟨x, hx, rfl⟩
    exact (strict_margin_of_strict_alloc u R h1 q hq (hsep x hx y hy) hab).le
  · intro x hx
    exact csInf_le hbelow ⟨x, hx, rfl⟩

/-- Complete two-outcome pricing, including unattained price thresholds. -/
theorem implementable_of_two_outcomes (u : A → Θ → ℝ) (R : A → A → Prop)
    (hbdd : IsBoundedTypeSpace u) (h1 : OneDimensional u R)
    (q : Θ → A) (hq : MonotoneWRT u R q)
    {a b : A} (hab : StrictPart R a b)
    (hrange : ∀ x, q x = a ∨ q x = b) : Implementable u q := by
  classical
  by_cases hH : (q ⁻¹' {a}).Nonempty
  · obtain ⟨price, hlow, hhigh⟩ := exists_separating_price u R hbdd h1 q hq
      (q ⁻¹' {a}) (q ⁻¹' {b}) hH (by
        intro x hx y hy
        have hx' : q x = a := hx
        have hy' : q y = b := hy
        simpa only [hx', hy'] using hab) hab
    have hba : b ≠ a := by intro h; subst b; exact hab.2 hab.1
    refine ⟨fun x => if q x = a then price else 0, ?_⟩
    intro x y
    change u (q y) x - (if q y = a then price else 0) ≤
      u (q x) x - (if q x = a then price else 0)
    rcases hrange x with hx | hx <;> rcases hrange y with hy | hy
    · simp [hx, hy]
    · have h := hhigh x hx
      simp only [hx, hy, eq_self, ite_true, if_neg hba]
      linarith
    · have h := hlow x hx
      simp only [hx, hy, eq_self, ite_true, if_neg hba]
      linarith
    · simp [hx, hy]
  · apply implementable_of_constant u q
    intro x y
    have hnot : ∀ z, q z ≠ a := by
      intro z hz
      exact hH ⟨z, hz⟩
    exact ((hrange x).resolve_left (hnot x)).trans
      ((hrange y).resolve_left (hnot y)).symm

/-- Adjacent comparisons suffice to identify a maximum in a finite sequence. -/
theorem finite_score_max (f : ℕ → ℝ) (n k : ℕ) (_hk : k ≤ n)
    (hup : ∀ j, j < k → f j ≤ f (j + 1))
    (hdown : ∀ j, k ≤ j → j < n → f (j + 1) ≤ f j)
    (j : ℕ) (hj : j ≤ n) : f j ≤ f k := by
  rcases le_total j k with hjk | hkj
  · have rise : ∀ l, j ≤ l → l ≤ k → f j ≤ f l := by
      intro l hjl
      induction l, hjl using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ l hjl ih =>
        intro hl
        exact (ih (by omega)).trans (hup l (by omega))
    exact rise k hjk le_rfl
  · have fall : ∀ l, k ≤ l → l ≤ n → f l ≤ f k := by
      intro l hkl
      induction l, hkl using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ l hkl ih =>
        intro hl
        exact (hdown l hkl (by omega)).trans (ih (by omega))
    exact fall j hkj hj

/-- Finite adjacent price gaps imply all incentive constraints by telescoping.
Enumeration of allocation classes and construction of these gaps remain
separate obligations for the full finite-allocation theorem. -/
theorem implementable_of_chain_prices (u : A → Θ → ℝ) (q : Θ → A)
    (n : ℕ) (a : ℕ → A) (index : Θ → ℕ) (price : ℕ → ℝ)
    (hindex : ∀ x, index x ≤ n) (halloc : ∀ x, q x = a (index x))
    (hgap : ∀ x j, j < n →
      (j < index x → price (j + 1) - price j ≤ u (a (j + 1)) x - u (a j) x) ∧
      (index x ≤ j → u (a (j + 1)) x - u (a j) x ≤ price (j + 1) - price j)) :
    Implementable u q := by
  refine ⟨fun x => price (index x), ?_⟩
  intro x y
  change u (q y) x - price (index y) ≤ u (q x) x - price (index x)
  rw [halloc y, halloc x]
  apply finite_score_max (fun j => u (a j) x - price j) n (index x) (hindex x)
  · intro j hj
    have h := (hgap x j (by have := hindex x; omega)).1 hj
    linarith
  · intro j hj hjn
    have h := (hgap x j hjn).2 hj
    linarith
  · exact hindex y

/-- A pair of ordered types embeds the outcome preorder into real scores.
Equal scores retain precisely the original indifference classes. -/
theorem score_order (u : A → Θ → ℝ) (R : A → A → Prop)
    (hR : IsCompleteTransitive R) {x y : Θ} (hxy : HigherType u R x y)
    (a b : A) : R a b ↔ u b x - u b y ≤ u a x - u a y := by
  constructor
  · intro hab
    by_cases hba : R b a
    · have h := (hxy.2 a b ⟨hab, hba⟩)
      linarith [h.1, h.2]
    · have h := hxy.1 a b ⟨hab, hba⟩
      linarith
  · intro hscore
    by_contra hab
    have hba : R b a := (hR.1 a b).resolve_left hab
    have h := hxy.1 b a ⟨hba, hab⟩
    linarith

theorem score_strict_order (u : A → Θ → ℝ) (R : A → A → Prop)
    (hR : IsCompleteTransitive R) {x y : Θ} (hxy : HigherType u R x y)
    (a b : A) : StrictPart R a b ↔ u b x - u b y < u a x - u a y := by
  simp only [StrictPart, score_order u R hR hxy, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem implementable_of_utility_equivalent (u : A → Θ → ℝ)
    (q q' : Θ → A) (h : ∀ x y, u (q x) y = u (q' x) y)
    (hq' : Implementable u q') : Implementable u q := by
  obtain ⟨t, ht⟩ := hq'
  refine ⟨t, ?_⟩
  intro x y
  change u (q y) x - t y ≤ u (q x) x - t x
  rw [h y x, h x x]
  exact ht x y

end RochetFinitePricing

set_option autoImplicit false
namespace RochetFinitePricing
open MechanismDesign.IncentiveCompat
variable {A Θ : Type*}

/-- Construct all adjacent price gaps for a finite strict allocation chain,
and verify every report using the finite-score maximum lemma. -/
theorem implementable_of_strict_chain (u : A → Θ → ℝ) (R : A → A → Prop)
    (hbdd : IsBoundedTypeSpace u) (h1 : OneDimensional u R)
    (q : Θ → A) (hq : MonotoneWRT u R q)
    (n : ℕ) (a : ℕ → A) (index : Θ → ℕ)
    (hindex : ∀ x, index x ≤ n) (halloc : ∀ x, q x = a (index x))
    (hrep : ∀ j, j ≤ n → ∃ x, index x = j)
    (hstrict : ∀ i j, i < j → j ≤ n → StrictPart R (a j) (a i)) :
    Implementable u q := by
  classical
  have gaps : ∀ j : Fin n, ∃ price : ℝ,
      (∀ x, index x ≤ j.val → u (a (j.val + 1)) x - u (a j.val) x ≤ price) ∧
      (∀ x, j.val < index x → price ≤ u (a (j.val + 1)) x - u (a j.val) x) := by
    intro j
    have hH : {x : Θ | j.val < index x}.Nonempty := by
      obtain ⟨x, hx⟩ := hrep n le_rfl
      exact ⟨x, by simpa [hx] using j.isLt⟩
    obtain ⟨price, hlo, hhi⟩ := exists_separating_price u R hbdd h1 q hq
      {x | j.val < index x} {x | index x ≤ j.val} hH (by
        intro x hx y hy
        change j.val < index x at hx
        change index y ≤ j.val at hy
        rw [halloc x, halloc y]
        exact hstrict (index y) (index x) (by omega) (hindex x))
      (hstrict j.val (j.val + 1) (by omega) (by omega))
    exact ⟨price, hlo, hhi⟩
  choose gap hlo hhi using gaps
  let step : ℕ → ℝ := fun j => if hj : j < n then gap ⟨j, hj⟩ else 0
  let price : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, step j
  have hprice : ∀ j (hj : j < n), price (j + 1) - price j = gap ⟨j, hj⟩ := by
    intro j hj
    simp [price, Finset.sum_range_succ, step, hj]
  apply implementable_of_chain_prices u q n a index price hindex halloc
  intro x j hj
  rw [hprice j hj]
  exact ⟨fun hx => hhi ⟨j, hj⟩ x hx, fun hx => hlo ⟨j, hj⟩ x hx⟩

end RochetFinitePricing

set_option autoImplicit false
namespace RochetFinitePricing
open MechanismDesign.IncentiveCompat

theorem finite_monotone_of_ordered_pair {A Θ : Type*} [Finite A] [Nontrivial Θ]
    (u : A → Θ → ℝ) (R : A → A → Prop) (hR : IsCompleteTransitive R)
    (hbdd : IsBoundedTypeSpace u) (h1 : OneDimensional u R)
    (q : Θ → A) (hq : MonotoneWRT u R q)
    {x₀ y₀ : Θ} (hxy : HigherType u R x₀ y₀) : Implementable u q := by
  classical
  let score : A → ℝ := fun a => u a x₀ - u a y₀
  let s : Finset ℝ := ((Set.toFinite (Set.range q)).image score).toFinset
  have hmem : ∀ x, score (q x) ∈ s := by
    intro x
    change score (q x) ∈ ((Set.toFinite (Set.range q)).image score).toFinset
    simp only [Set.Finite.mem_toFinset, Set.mem_image]
    exact ⟨q x, ⟨x, rfl⟩, rfl⟩
  have hs : 0 < s.card := Finset.card_pos.mpr ⟨score (q x₀), hmem x₀⟩
  let n := s.card - 1
  have hcard : s.card = n + 1 := by dsimp [n]; omega
  let enum : Fin (n + 1) ≃o s := s.orderIsoOfFin hcard
  have hrepr : ∀ i : Fin (n + 1), ∃ x, score (q x) = (enum i).val := by
    intro i
    have h := (enum i).property
    change (enum i).val ∈ ((Set.toFinite (Set.range q)).image score).toFinset at h
    simp only [Set.Finite.mem_toFinset, Set.mem_image, Set.mem_range] at h
    obtain ⟨a, ⟨x, rfl⟩, ha⟩ := h
    exact ⟨x, ha⟩
  choose rep hrepScore using hrepr
  let idx : Θ → Fin (n + 1) := fun x => enum.symm ⟨score (q x), hmem x⟩
  have hidx : ∀ x, (enum (idx x)).val = score (q x) := by
    intro x
    exact congrArg Subtype.val (enum.apply_symm_apply _)
  let a : ℕ → A := fun j => q (rep ⟨min j n, by omega⟩)
  let index : Θ → ℕ := fun x => (idx x).val
  have ha : ∀ j (hj : j ≤ n), score (a j) = (enum ⟨j, by omega⟩).val := by
    intro j hj
    simpa only [a, min_eq_left hj] using hrepScore ⟨j, by omega⟩
  have hindex : ∀ x, index x ≤ n := by intro x; exact Nat.le_of_lt_succ (idx x).isLt
  have hscore : ∀ x, score (a (index x)) = score (q x) := by
    intro x
    rw [ha (index x) (hindex x)]
    exact hidx x
  let q' : Θ → A := fun x => a (index x)
  have hequiv : ∀ x y, u (q x) y = u (q' x) y := by
    intro x y
    apply utility_eq_of_indiff u R h1
    constructor
    · apply (score_order u R hR hxy _ _).mpr
      change score (a (index x)) ≤ score (q x)
      exact (hscore x).le
    · apply (score_order u R hR hxy _ _).mpr
      change score (q x) ≤ score (a (index x))
      exact (hscore x).ge
  have hq' : MonotoneWRT u R q' := by
    intro x y htypes
    apply (score_order u R hR hxy _ _).mpr
    change score (a (index y)) ≤ score (a (index x))
    rw [hscore y, hscore x]
    exact (score_order u R hR hxy _ _).mp (hq x y htypes)
  have hrep : ∀ j, j ≤ n → ∃ x, index x = j := by
    intro j hj
    let i : Fin (n + 1) := ⟨j, by omega⟩
    refine ⟨rep i, ?_⟩
    have hi : idx (rep i) = i := by
      apply enum.injective
      apply Subtype.ext
      exact (hidx (rep i)).trans (hrepScore i)
    exact congrArg Fin.val hi
  have hstrict : ∀ i j, i < j → j ≤ n → StrictPart R (a j) (a i) := by
    intro i j hij hj
    apply (score_strict_order u R hR hxy _ _).mpr
    change score (a i) < score (a j)
    rw [ha i (by omega), ha j hj]
    exact enum.strictMono (show (⟨i, by omega⟩ : Fin (n + 1)) < ⟨j, by omega⟩ from hij)
  apply implementable_of_utility_equivalent u q q' hequiv
  exact implementable_of_strict_chain u R hbdd h1 q' hq' n a index hindex
    (fun _ => rfl) hrep hstrict

end RochetFinitePricing
open MechanismDesign.IncentiveCompat
theorem solution {A Θ : Type*} [Finite A] [Nonempty Θ] (u : A → Θ → ℝ)
    (R : A → A → Prop) (hR : IsCompleteTransitive R) (hbdd : IsBoundedTypeSpace u)
    (h1 : OneDimensional u R) (q : Θ → A) (hq : MonotoneWRT u R q) :
    Implementable u q := by
  classical
  cases subsingleton_or_nontrivial Θ with
  | inl h =>
    letI := h
    apply RochetFinitePricing.implementable_of_constant u q
    intro x y
    exact congrArg q (Subsingleton.elim x y)
  | inr h =>
    letI := h
    obtain ⟨x, y, hne⟩ := exists_pair_ne Θ
    rcases h1 x y hne with hxy | hyx
    · exact RochetFinitePricing.finite_monotone_of_ordered_pair u R hR hbdd h1 q hq hxy
    · exact RochetFinitePricing.finite_monotone_of_ordered_pair u R hR hbdd h1 q hq hyx

#print axioms solution
