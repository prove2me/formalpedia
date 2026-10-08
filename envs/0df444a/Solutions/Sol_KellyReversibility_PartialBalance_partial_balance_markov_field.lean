-- Prove2me | solution 1 for KellyReversibility.PartialBalance.partial_balance_markov_field
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T06:35:38.529474+00:00
-- url     : https://prove2.me/submissions/942660ad-1cd6-46a5-aa72-c77b36c7b79a

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

set_option autoImplicit false

namespace CD0CaffdHelpers

open KellyReversibility.PartialBalance

/-- Two positive balance vectors of a finite irreducible rate matrix are proportional. -/
theorem balance_vec_proportional {α : Type*} [Fintype α] [Nonempty α] (R : α → α → ℝ)
    (hR0 : ∀ a b, a ≠ b → 0 ≤ R a b) (hRd : ∀ a, R a a = 0)
    (hirr : ∀ b a0, Relation.ReflTransGen (fun a b => 0 < R a b) b a0)
    (x y : α → ℝ) (hx : ∀ a, 0 < x a) (hy : ∀ a, 0 < y a)
    (hbx : ∀ c, x c * ∑ b, R c b = ∑ b, x b * R b c)
    (hby : ∀ c, y c * ∑ b, R c b = ∑ b, y b * R b c) :
    ∃ k, 0 < k ∧ ∀ a, x a = k * y a := by
  obtain ⟨a0, -, ha0⟩ :=
    Finset.exists_min_image Finset.univ (fun a => x a / y a) Finset.univ_nonempty
  set k := x a0 / y a0 with hk
  have hkpos : 0 < k := div_pos (hx a0) (hy a0)
  set z : α → ℝ := fun a => x a - k * y a with hz
  have hz0 : ∀ a, 0 ≤ z a := by
    intro a
    have h1 := ha0 a (Finset.mem_univ a)
    have h2 : k * y a ≤ x a := (le_div_iff₀ (hy a)).1 h1
    show 0 ≤ x a - k * y a
    linarith
  have hza0 : z a0 = 0 := by
    show x a0 - k * y a0 = 0
    rw [hk, div_mul_cancel₀ _ (hy a0).ne', sub_self]
  have hbz : ∀ c, z c * ∑ b, R c b = ∑ b, z b * R b c := by
    intro c
    have e1 : ∑ b, z b * R b c = ∑ b, x b * R b c - k * ∑ b, y b * R b c := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hz]
      ring
    rw [e1, ← hbx c, ← hby c]
    simp only [hz]
    ring
  have hprop : ∀ b c, z c = 0 → 0 < R b c → z b = 0 := by
    intro b c hc hR
    have hsum : ∑ b, z b * R b c = 0 := by rw [← hbz c, hc, zero_mul]
    have hnn : ∀ i ∈ (Finset.univ : Finset α), 0 ≤ z i * R i c := by
      intro i _
      by_cases hic : i = c
      · subst hic; rw [hRd]; simp
      · exact mul_nonneg (hz0 i) (hR0 i c hic)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum b (Finset.mem_univ b)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hR.ne'
  refine ⟨k, hkpos, fun a => ?_⟩
  have : z a = 0 := by
    induction hirr a a0 using Relation.ReflTransGen.head_induction_on with
    | refl => exact hza0
    | head hbc _ hc => exact hprop _ _ hc hbc
  have h3 : x a - k * y a = 0 := this
  linarith

theorem frozen_rates_eq {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (j : ι) (n n' : ∀ i, N i) (h : ∀ i, G.Adj j i → n i = n' i) (a b : N j) :
    q (Function.update n j a) (Function.update n j b) =
      q (Function.update n' j a) (Function.update n' j b) := by
  have := hsp.2.2.1 j b (Function.update n j a) (Function.update n' j a) (by simp)
    (fun i hi => by simp [Function.update_of_ne hi.ne', h i hi])
  simpa [Function.update_idem] using this

theorem frozen_balance {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, Fintype (N i)]
    (π : (∀ i, N i) → ℝ) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι)
    (hpb : SitePartialBalance π q j) (n : ∀ i, N i) (c : N j) :
    π (Function.update n j c) * ∑ m, q (Function.update n j c) (Function.update n j m) =
      ∑ m, π (Function.update n j m) * q (Function.update n j m) (Function.update n j c) := by
  simpa [Function.update_idem] using hpb (Function.update n j c)

theorem chain_transport {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    (q : (∀ i, N i) → (∀ i, N i) → ℝ) (j : ι) (n : ∀ i, N i) (s t : ∀ i, N i)
    (h : Relation.ReflTransGen
      (fun a b : (∀ i, N i) => (∃ m' : N j, b = Function.update a j m') ∧ 0 < q a b) s t)
    (hs : s = Function.update n j (s j)) :
    t = Function.update n j (t j) ∧
      Relation.ReflTransGen
        (fun a b : N j => 0 < q (Function.update n j a) (Function.update n j b)) (s j) (t j) := by
  induction h with
  | refl => exact ⟨hs, Relation.ReflTransGen.refl⟩
  | @tail b c _ hst ih =>
    obtain ⟨ht, hr⟩ := ih
    obtain ⟨⟨m', rfl⟩, hpos⟩ := hst
    have e : Function.update b j m' = Function.update n j m' := by
      calc Function.update b j m' = Function.update (Function.update n j (b j)) j m' := by
            rw [← ht]
        _ = Function.update n j m' := Function.update_idem _ _ _
    refine ⟨?_, hr.tail ?_⟩
    · rw [Function.update_self]; exact e
    · rw [Function.update_self, ← ht, ← e]; exact hpos

theorem frozen_irred {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (j : ι) (n : ∀ i, N i) (b a0 : N j) :
    Relation.ReflTransGen
      (fun a b : N j => 0 < q (Function.update n j a) (Function.update n j b)) b a0 := by
  have h := hsp.2.2.2 j a0 (Function.update n j b)
  have := (chain_transport q j n _ _ h (by simp)).2
  simpa only [Function.update_self] using this

end CD0CaffdHelpers

open KellyReversibility.PartialBalance in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ι → Type*} [∀ i, Fintype (N i)] [∀ i, DecidableEq (N i)]
    (G : SimpleGraph ι) (q : (∀ i, N i) → (∀ i, N i) → ℝ) (hsp : IsSpatialProcess G q)
    (π : (∀ i, N i) → ℝ) (hπ : IsEquilibriumDist q π)
    (hstates : ∃ n n' : (∀ i, N i), n ≠ n')
    (hpb : ∀ j : ι, SitePartialBalance π q j) :
    IsMarkovField G π := by
  have hs : ∑ n, π n = 1 := by
    have := hπ.2.1
    rwa [tsum_fintype] at this
  refine ⟨fun n => ⟨hπ.1 n, ?_⟩, hs, fun j n n' hj hadj => ?_⟩
  · obtain ⟨n1, n2, hne⟩ := hstates
    obtain ⟨m, hmn⟩ : ∃ m, n ≠ m := by
      by_cases h : n1 = n
      · exact ⟨n2, h ▸ hne⟩
      · exact ⟨n1, fun e => h e.symm⟩
    have hle : π n + π m ≤ ∑ x, π x := by
      rw [← Finset.sum_pair hmn]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => (hπ.1 i).le)
    have := hπ.1 m
    linarith
  · have : Nonempty (N j) := ⟨n j⟩
    obtain ⟨k, hk, hxy⟩ := CD0CaffdHelpers.balance_vec_proportional
      (fun a b => q (Function.update n' j a) (Function.update n' j b))
      (fun a b hab => hsp.1.1 _ _ (fun h => hab (by simpa using congrFun h j)))
      (fun a => hsp.1.2 _)
      (CD0CaffdHelpers.frozen_irred G q hsp j n')
      (fun a => π (Function.update n j a)) (fun a => π (Function.update n' j a))
      (fun a => hπ.1 _) (fun a => hπ.1 _)
      (fun c => by
        have := CD0CaffdHelpers.frozen_balance π q j (hpb j) n c
        simp only [CD0CaffdHelpers.frozen_rates_eq G q hsp j n n' hadj] at this
        exact this)
      (fun c => CD0CaffdHelpers.frozen_balance π q j (hpb j) n' c)
    have e1 : condProb π j n = π (Function.update n j (n j)) / ∑ m, π (Function.update n j m) := by
      rw [Function.update_eq_self]; rfl
    have e2 : condProb π j n' =
        π (Function.update n' j (n j)) / ∑ m, π (Function.update n' j m) := by
      rw [hj, Function.update_eq_self]; rfl
    rw [e1, e2]
    simp only [hxy]
    rw [← Finset.mul_sum, mul_div_mul_left _ _ hk.ne']
