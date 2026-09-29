-- Prove2me | solution 1 for HarelTarjan.Compressed.rank_ge_count
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T06:27:56.640648+00:00
-- url     : https://prove2.me/submissions/01931bf6-59ac-4d13-9f81-cb249713fdba

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree
import Theorems.Thm_HarelTarjan_Compressed_lemma8_rank_count

open HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 9, first sentence** (Harel–Tarjan, p. 345). At most `n / 2^{k-1}` vertices have rank
`k` or greater, stated without division as `#{v : rank(v) ≥ k} · 2^k ≤ 2n`.

Summing the rank-`i` bound of Lemma 8 gives `Σ_{i ≥ k} n/2^i = n/2^{k-1}`. The summation is
formalized by the recursion `A_k = N_k + A_{k+1}` between the "rank at least `k`" count `A_k` and
the "rank exactly `k`" count `N_k`, together with the geometric bound `2·A_k ≤ n + A_{k+1}`: this
is exactly the tail-sum estimate `A_k = Σ_{i≥k} N_i ≤ Σ_{i≥k} n/2^i`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V) (k : ℕ) :
    (Finset.univ.filter (fun v => k ≤ rank T v)).card * 2 ^ k ≤ 2 * Fintype.card V := by
  classical
  set M : ℕ := Fintype.card V with hM
  set K : ℕ := M + 1 with hK
  -- Every rank is at most `M`: `rank v ≤ size_C v ≤ n`.
  have hrank_le : ∀ v : V, rank T v ≤ M := by
    intro v
    calc rank T v ≤ sizeC T v := Nat.log_le_self 2 (sizeC T v)
      _ ≤ M := by
          rw [hM]
          show (Finset.univ.filter (fun u => IsAncestorC T v u)).card ≤ Fintype.card V
          rw [← Finset.card_univ]
          exact Finset.card_le_card (fun u _ => Finset.mem_univ u)
  -- Splitting off the vertices of rank exactly `k`.
  have hrec : ∀ k : ℕ, (Finset.univ.filter (fun v => k ≤ rank T v)).card =
      (Finset.univ.filter (fun v => rank T v = k)).card
        + (Finset.univ.filter (fun v => k + 1 ≤ rank T v)).card := by
    intro k
    have hunion : Finset.univ.filter (fun v => k ≤ rank T v) =
        Finset.univ.filter (fun v => rank T v = k)
          ∪ Finset.univ.filter (fun v => k + 1 ≤ rank T v) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.univ.filter (fun v => rank T v = k))
        (Finset.univ.filter (fun v => k + 1 ≤ rank T v)) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- `A_{K-j} · 2^{K-j} ≤ 2n` by descending induction, since `A_K = 0`.
  have key : ∀ j : ℕ,
      (Finset.univ.filter (fun v => K - j ≤ rank T v)).card * 2 ^ (K - j) ≤ 2 * M := by
    intro j
    induction j with
    | zero =>
      have hzero : (Finset.univ.filter (fun v => K - 0 ≤ rank T v)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero] at hv
        have := hrank_le v
        omega
      rw [hzero]
      simp
    | succ j ih =>
      by_cases hj : j < K
      · have hks : K - (j + 1) + 1 = K - j := by omega
        have hN : (Finset.univ.filter (fun v => rank T v = K - (j + 1))).card
            * 2 ^ (K - (j + 1)) ≤ M := by
          rw [hM]
          exact lemma8_rank_count T (K - (j + 1))
        have hIH : (Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card
            * 2 ^ (K - (j + 1) + 1) ≤ 2 * M := by
          rw [hks]
          exact ih
        -- `2 · A_k · 2^k = N_k · 2^{k+1} + A_{k+1} · 2^{k+1} ≤ 2n + 2n`
        have h2 : 2 * ((Finset.univ.filter (fun v => K - (j + 1) ≤ rank T v)).card
            * 2 ^ (K - (j + 1))) ≤ 2 * (2 * M) := by
          rw [hrec (K - (j + 1))]
          have hA : 2 * ((Finset.univ.filter (fun v => rank T v = K - (j + 1))).card
              * 2 ^ (K - (j + 1))) ≤ 2 * M := Nat.mul_le_mul_left 2 hN
          have hB : 2 * ((Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card
              * 2 ^ (K - (j + 1))) ≤ 2 * M := by
            have hp : 2 * ((Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card
                * 2 ^ (K - (j + 1)))
                = (Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card
                  * 2 ^ (K - (j + 1) + 1) := by
              rw [pow_succ']
              ring
            rw [hp]
            exact hIH
          calc 2 * (((Finset.univ.filter (fun v => rank T v = K - (j + 1))).card
                  + (Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card)
                  * 2 ^ (K - (j + 1)))
              = 2 * ((Finset.univ.filter (fun v => rank T v = K - (j + 1))).card
                  * 2 ^ (K - (j + 1)))
                + 2 * ((Finset.univ.filter (fun v => K - (j + 1) + 1 ≤ rank T v)).card
                  * 2 ^ (K - (j + 1))) := by ring
            _ ≤ 2 * M + 2 * M := add_le_add hA hB
            _ = 2 * (2 * M) := by ring
        omega
      · have hsame : K - (j + 1) = K - j := by omega
        rw [hsame]
        exact ih
  by_cases hk : k ≤ K
  · have h1 : K - (K - k) = k := by omega
    have hfin := key (K - k)
    simp_rw [h1] at hfin
    exact hfin
  · have hzero : (Finset.univ.filter (fun v => k ≤ rank T v)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have := hrank_le v
      omega
    rw [hzero]
    simp
