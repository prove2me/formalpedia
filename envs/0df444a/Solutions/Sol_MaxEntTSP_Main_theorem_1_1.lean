-- Prove2me | solution 1 for MaxEntTSP.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:13:47.471529+00:00
-- url     : https://prove2.me/submissions/1b158193-a284-41e0-9017-327d991d592a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model
import Theorems.Thm_MetricTSP_held_karp_le_opt
import Theorems.Thm_MaxEntTSP_Main_node_split
import Theorems.Thm_MaxEntTSP_Main_fact_2_2
import Theorems.Thm_MaxEntTSP_Main_ojoin_bound

open MaxEntTSP.Main MetricTSP Finset

/-- Double sum of a symmetric, zero-diagonal function equals twice the sum over
off-diagonal unordered pairs. -/
private lemma double_sum_eq_two_sym2 {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      2 * ∑ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => ¬ e.IsDiag),
        Sym2.lift ⟨f, hs⟩ e := by
  rw [← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : Fin m × Fin m => s(p.1, p.2))
    (t := (univ : Finset (Sym2 (Fin m)))) (fun _ _ => mem_univ _)]
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not univ (fun e : Sym2 (Fin m) => e.IsDiag)]
  have h1 : ∀ e ∈ (univ : Finset (Sym2 (Fin m))).filter (fun e => e.IsDiag),
      (∑ p ∈ (univ ×ˢ univ : Finset (Fin m × Fin m)) with s(p.1, p.2) = e, f p.1 p.2) = 0 := by
    intro e he
    rw [mem_filter] at he
    apply Finset.sum_eq_zero
    intro p hp
    rw [mem_filter] at hp
    have : (s(p.1, p.2)).IsDiag := hp.2 ▸ he.2
    obtain ⟨a, b⟩ := p
    rw [Sym2.mk_isDiag_iff] at this
    simp only
    simp only at this; rw [this, hd]
  rw [Finset.sum_eq_zero h1, zero_add]
  apply Finset.sum_congr rfl
  intro e he
  rw [mem_filter] at he
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using he.2
    have hfib : ((univ ×ˢ univ : Finset (Fin m × Fin m)).filter
        (fun p => s(p.1, p.2) = s(a, b))) = {(a, b), (b, a)} := by
      ext ⟨p, q⟩
      simp only [mem_filter, mem_product, mem_univ, true_and, mem_insert, mem_singleton,
        Sym2.eq_iff, Prod.mk.injEq]
    rw [hfib, Finset.sum_pair (by simp [Prod.mk.injEq, hab])]
    simp only [Sym2.lift_mk]
    rw [hs b a]
    ring

private lemma pairCost_mk {m : ℕ} (c : Fin m → Fin m → ℝ) (hs : ∀ i j, c i j = c j i)
    (i j : Fin m) : pairCost c s(i, j) = c i j := by
  simp only [pairCost, Sym2.lift_mk]
  rw [hs j i]; ring

/-- The support sum of `c · x` equals half the double sum. -/
private lemma support_sum_eq {m : ℕ} (c x : Fin m → Fin m → ℝ)
    (hcs : ∀ i j, c i j = c j i) (hxs : ∀ i j, x i j = x j i)
    (hxd : ∀ i, x i i = 0) (hx0 : ∀ i j, 0 ≤ x i j) (a b : Fin m) (hcab : c a b = 0) :
    (∑ e ∈ lpSupport x a b, pairCost c e * pairCost x e) =
      (1 / 2) * ∑ i, ∑ j, c i j * x i j := by
  have hs : ∀ i j, c i j * x i j = c j i * x j i := fun i j => by rw [hcs, hxs]
  rw [double_sum_eq_two_sym2 (fun i j => c i j * x i j) hs (fun i => by simp [hxd])]
  rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  have hg : ∀ e : Sym2 (Fin m), pairCost c e * pairCost x e =
      Sym2.lift ⟨fun i j => c i j * x i j, hs⟩ e := by
    intro e
    induction e using Sym2.ind with
    | h i j => rw [pairCost_mk c hcs, pairCost_mk x hxs, Sym2.lift_mk]
  simp_rw [hg]
  unfold lpSupport
  apply Finset.sum_subset
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact he.1
  · intro e he hne
    simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at he hne
    rw [← hg]
    by_cases hab : e = s(a, b)
    · subst hab; rw [pairCost_mk c hcs, hcab, zero_mul]
    · have hle := hne he hab
      have hge : 0 ≤ pairCost x e := by
        induction e using Sym2.ind with
        | h i j => rw [pairCost_mk x hxs]; exact hx0 i j
      rw [le_antisymm hle hge, mul_zero]

theorem solution :
    ∃ ε : ℝ, 1 / 10 ^ 36 < ε ∧
      ∀ (n : ℕ), 3 ≤ n →
      ∀ c : Fin n → Fin n → ℝ, IsMetricCost c →
      ∀ x : Fin n → Fin n → ℝ, IsHeldKarp x →
        (1 / 2) * (∑ i, ∑ j, c i j * x i j) = hkValue c →
      ∀ (u : Fin n) (μ : Finset (Sym2 (Fin (n + 1))) → ℝ),
        IsMaxEntropy (lpSupport (splitLP x u) (u0 u) (v0 n)) (splitLP x u) μ →
        algCost (splitCost c u) μ ≤ (3 / 2 - ε) * tspOpt c := by
  refine ⟨(312 / 10 ^ 18 : ℝ) * ((312 / 10 ^ 18) * 10 / (1308 * 41)) / 6, by norm_num, ?_⟩
  intro n hn c hc x hx hopt u μ hμ
  obtain ⟨hc', hx', _, hsum, _⟩ := node_split n hn c x hc hx hopt u
  have hojoin := ojoin_bound n hn c x hc hx hopt u μ hμ
  simp only at hojoin
  have hHK := held_karp_le_opt n hn c hc
  have hab : u0 u ≠ v0 n := by
    simp [u0, v0, Fin.castSucc_ne_last]
  have hcost0 : splitCost c u (u0 u) (v0 n) = 0 := by
    simp only [splitCost, proj, u0, v0, Fin.lastCases_last, Fin.lastCases_castSucc, id]
    exact hc.2.1 u
  have h22 := fact_2_2 (n + 1) (splitLP x u) (splitCost c u) hc' (u0 u) (v0 n) hab hcost0 μ hμ.1
  have hpc0 : pairCost (splitCost c u) s(u0 u, v0 n) = 0 := by
    rw [pairCost_mk _ hc'.1, hcost0]
  have htree : (∑ T, μ T * treeCost (splitCost c u) T) =
      ∑ T, μ T * treeCost (splitCost c u) (insert (s(u0 u, v0 n)) T) := by
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : μ T = 0
    · rw [hT, zero_mul, zero_mul]
    · have hsub : T ⊆ lpSupport (splitLP x u) (u0 u) (v0 n) := (hμ.1.2.1 T hT).1
      have hn : s(u0 u, v0 n) ∉ T := by
        intro h
        have := hsub h
        simp [lpSupport] at this
      rw [treeCost, treeCost, Finset.sum_insert hn, hpc0, zero_add]
  rw [h22, support_sum_eq _ _ hc'.1 hx'.1 hx'.2.1 hx'.2.2.1 _ _ hcost0, hsum, hopt] at htree
  have halg : algCost (splitCost c u) μ =
      (∑ T, μ T * treeCost (splitCost c u) T) +
        ∑ T, μ T * minMatchCost (splitCost c u) T := by
    rw [algCost, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _; ring
  rw [halg, htree]
  linarith
