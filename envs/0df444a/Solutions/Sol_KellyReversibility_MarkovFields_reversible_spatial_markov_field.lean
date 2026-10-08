-- Prove2me | solution 1 for KellyReversibility.MarkovFields.reversible_spatial_markov_field
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:59:54.66582+00:00
-- url     : https://prove2.me/submissions/6ece1c23-b844-43d6-aec9-bce15076a21b

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_MarkovFields_RandomField
import Definitions.Def_KellyReversibility_MarkovFields_SpatialProcess

set_option autoImplicit false

namespace KRMF09f

open KellyReversibility.MarkovFields

theorem upd_of_agree {V : Type*} [DecidableEq V] {N : V → Type*} {a c : (k : V) → N k} {j : V}
    (hc : ∀ k, k ≠ j → c k = a k) : c = Function.update a j (c j) := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Function.update_of_ne h, hc k h]

theorem transport {V : Type*} [DecidableEq V] {N : V → Type*} (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ) (π : ((j : V) → N j) → ℝ)
    (h2 : ∀ (j : V) (m : N j) (n n' : (k : V) → N k), n j = n' j →
      (∀ k, G.Adj j k → n k = n' k) →
      q n (Function.update n j m) = q n' (Function.update n' j m))
    (hpos : ∀ x, 0 < π x) (hdb : KellyStochasticNetworks.DetailedBalance π q)
    (j : V) (n n' : (k : V) → N k) (hagree : ∀ k, G.Adj j k → n' k = n k)
    (a0 a : (k : V) → N k) (ha0 : ∀ k, k ≠ j → a0 k = n k)
    (hr : Relation.ReflTransGen
      (fun a b : (k : V) → N k => 0 < q a b ∧ ∀ k, k ≠ j → b k = a k) a0 a) :
    (∀ k, k ≠ j → a k = n k) ∧
      π a * π (Function.update n' j (a0 j)) = π (Function.update n' j (a j)) * π a0 := by
  induction hr with
  | refl => exact ⟨ha0, mul_comm _ _⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hqbc, hoff⟩ := hbc
    obtain ⟨hb, ihe⟩ := ih
    have hc : ∀ k, k ≠ j → c k = n k := fun k hk => (hoff k hk).trans (hb k hk)
    refine ⟨hc, ?_⟩
    have hcb : c = Function.update b j (c j) := upd_of_agree hoff
    have hbc' : b = Function.update c j (b j) := upd_of_agree (fun k hk => (hoff k hk).symm)
    have hCB : Function.update n' j (c j) =
        Function.update (Function.update n' j (b j)) j (c j) := by simp
    have hBC : Function.update n' j (b j) =
        Function.update (Function.update n' j (c j)) j (b j) := by simp
    have hadjB : ∀ k, G.Adj j k → b k = Function.update n' j (b j) k := fun k hk => by
      have hkj : k ≠ j := (G.ne_of_adj hk).symm
      rw [Function.update_of_ne hkj, hb k hkj, hagree k hk]
    have hadjC : ∀ k, G.Adj j k → c k = Function.update n' j (c j) k := fun k hk => by
      have hkj : k ≠ j := (G.ne_of_adj hk).symm
      rw [Function.update_of_ne hkj, hc k hkj, hagree k hk]
    have e1 : q b c = q (Function.update n' j (b j)) (Function.update n' j (c j)) := by
      have := h2 j (c j) b (Function.update n' j (b j)) (by simp) hadjB
      rw [← hcb, ← hCB] at this
      exact this
    have e2 : q c b = q (Function.update n' j (c j)) (Function.update n' j (b j)) := by
      have := h2 j (b j) c (Function.update n' j (c j)) (by simp) hadjC
      rw [← hbc', ← hBC] at this
      exact this
    have db1 := hdb b c
    have db2 := hdb (Function.update n' j (b j)) (Function.update n' j (c j))
    rw [← e1, ← e2] at db2
    have hqcb : 0 < q c b := by
      by_contra hneg
      replace hneg := not_lt.mp hneg
      nlinarith [hpos c, hpos b, mul_pos (hpos b) hqbc, mul_nonpos_of_nonneg_of_nonpos (hpos c).le hneg]
    apply mul_left_cancel₀ hqcb.ne'
    linear_combination (-(π (Function.update n' j (a0 j)))) * db1 + π a0 * db2 + q b c * ihe

theorem cross {V : Type*} [DecidableEq V] {N : V → Type*} (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ) (π : ((j : V) → N j) → ℝ)
    (h2 : ∀ (j : V) (m : N j) (n n' : (k : V) → N k), n j = n' j →
      (∀ k, G.Adj j k → n k = n' k) →
      q n (Function.update n j m) = q n' (Function.update n' j m))
    (h3 : ∀ (j : V) (m : N j) (n : (k : V) → N k),
      Relation.ReflTransGen
        (fun a b : (k : V) → N k => 0 < q a b ∧ ∀ k, k ≠ j → b k = a k)
        n (Function.update n j m))
    (hpos : ∀ x, 0 < π x) (hdb : KellyStochasticNetworks.DetailedBalance π q)
    (j : V) (n n' : (k : V) → N k) (hagree : ∀ k, G.Adj j k → n' k = n k) (m m' : N j) :
    π (Function.update n j m') * π (Function.update n' j m) =
      π (Function.update n' j m') * π (Function.update n j m) := by
  have hr := h3 j m' (Function.update n j m)
  rw [Function.update_idem] at hr
  have := (transport G q π h2 hpos hdb j n n' hagree (Function.update n j m)
    (Function.update n j m') (fun k hk => Function.update_of_ne hk _ _) hr).2
  simp only [Function.update_self] at this
  exact this

theorem swap {V : Type*} [DecidableEq V] {N : V → Type*} (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ) (π : ((j : V) → N j) → ℝ)
    (h2 : ∀ (j : V) (m : N j) (n n' : (k : V) → N k), n j = n' j →
      (∀ k, G.Adj j k → n k = n' k) →
      q n (Function.update n j m) = q n' (Function.update n' j m))
    (h3 : ∀ (j : V) (m : N j) (n : (k : V) → N k),
      Relation.ReflTransGen
        (fun a b : (k : V) → N k => 0 < q a b ∧ ∀ k, k ≠ j → b k = a k)
        n (Function.update n j m))
    (hpos : ∀ x, 0 < π x) (hdb : KellyStochasticNetworks.DetailedBalance π q)
    (j : V) (n n'' : (k : V) → N k) (hj : n'' j = n j)
    (hagree : ∀ k, G.Adj j k → n'' k = n k) (m : N j) :
    π n * π (Function.update n'' j m) = π n'' * π (Function.update n j m) := by
  have h := cross G q π h2 h3 hpos hdb j n n'' hagree (n j) m
  have e1 : Function.update n'' j (n j) = n'' := by
    rw [← hj]; exact Function.update_eq_self _ _
  rw [e1, Function.update_eq_self] at h
  linear_combination -h

theorem key {V : Type*} [Fintype V] [DecidableEq V] {N : V → Type*} [∀ j, Fintype (N j)]
    (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ) (π : ((j : V) → N j) → ℝ)
    (h2 : ∀ (j : V) (m : N j) (n n' : (k : V) → N k), n j = n' j →
      (∀ k, G.Adj j k → n k = n' k) →
      q n (Function.update n j m) = q n' (Function.update n' j m))
    (h3 : ∀ (j : V) (m : N j) (n : (k : V) → N k),
      Relation.ReflTransGen
        (fun a b : (k : V) → N k => 0 < q a b ∧ ∀ k, k ≠ j → b k = a k)
        n (Function.update n j m))
    (hpos : ∀ x, 0 < π x) (hdb : KellyStochasticNetworks.DetailedBalance π q)
    (j : V) (n : (k : V) → N k) (A D : Finset ((k : V) → N k))
    (hA : ∀ x, x ∈ A ↔ (x j = n j ∧ ∀ k ∈ G.neighborSet j, x k = n k))
    (hD : ∀ x, x ∈ D ↔ ∀ k ∈ G.neighborSet j, x k = n k) :
    π n / ∑ m : N j, π (Function.update n j m) = (∑ x ∈ A, π x) / ∑ x ∈ D, π x := by
  have hne : ∀ k ∈ G.neighborSet j, k ≠ j := fun k hk =>
    (G.ne_of_adj ((SimpleGraph.mem_neighborSet _ _ _).1 hk)).symm
  have hZ : 0 < ∑ m : N j, π (Function.update n j m) :=
    Finset.sum_pos (fun m _ => hpos _) ⟨n j, Finset.mem_univ _⟩
  have hnD : n ∈ D := (hD n).2 (fun k _ => rfl)
  have hDpos : 0 < ∑ x ∈ D, π x := Finset.sum_pos (fun x _ => hpos x) ⟨n, hnD⟩
  have hprod : ∑ x ∈ D, π x =
      ∑ p ∈ A ×ˢ (Finset.univ : Finset (N j)), π (Function.update p.1 j p.2) := by
    apply Finset.sum_nbij' (fun x => (Function.update x j (n j), x j))
      (fun p => Function.update p.1 j p.2)
    · intro x hx
      have hx' := (hD x).1 hx
      rw [Finset.mem_product]
      refine ⟨(hA _).2 ⟨by simp, fun k hk => ?_⟩, Finset.mem_univ _⟩
      show Function.update x j (n j) k = n k
      rw [Function.update_of_ne (hne k hk)]
      exact hx' k hk
    · intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨_, hp1k⟩ := (hA _).1 hp.1
      refine (hD _).2 (fun k hk => ?_)
      rw [Function.update_of_ne (hne k hk)]
      exact hp1k k hk
    · intro x _
      simp
    · intro p hp
      obtain ⟨hp1j, -⟩ := (hA _).1 (Finset.mem_product.1 hp).1
      simp [← hp1j]
    · intro x _
      simp
  have hreidx : ∑ x ∈ D, π x = ∑ a ∈ A, ∑ m : N j, π (Function.update a j m) := by
    rw [hprod, Finset.sum_product]
  rw [div_eq_div_iff hZ.ne' hDpos.ne', hreidx, Finset.mul_sum (s := A), Finset.sum_mul (s := A)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  obtain ⟨haj, hak⟩ := (hA a).1 ha
  exact swap G q π h2 h3 hpos hdb j n a haj
    (fun k hk => hak k ((SimpleGraph.mem_neighborSet _ _ _).2 hk)) m

end KRMF09f

open KellyReversibility.MarkovFields in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {N : V → Type*} [∀ j, Fintype (N j)] (G : SimpleGraph V)
    (q : ((j : V) → N j) → ((j : V) → N j) → ℝ)
    (hq_nonneg : ∀ n n', 0 ≤ q n n') (hq_diag : ∀ n, q n n = 0)
    (hspatial : IsSpatialProcess G q)
    (π : ((j : V) → N j) → ℝ) (hπ : IsRandomField π)
    (hdb : KellyStochasticNetworks.DetailedBalance π q) :
    IsMarkovField G π := by
  unfold IsMarkovField
  intro j n
  unfold condProb condProbGiven
  exact KRMF09f.key G q π hspatial.2.1 hspatial.2.2 hπ.1 hdb j n _ _
    (fun x => by simp) (fun x => by simp)
