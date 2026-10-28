-- Prove2me | solution 1 for GreedWorks.OnlineList.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:11:32.497437+00:00
-- url     : https://prove2.me/submissions/098fd109-eb51-456f-8e11-f0287177786e

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy

open MeasureTheory

namespace Aux_GreedWorks_lemma_4
open GreedWorks.OnlineList

variable {M : Type*} [Fintype M] [DecidableEq M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem mem_high (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n) :
    k ∈ high I j i ↔ I.weight j / mean I i j < I.weight k / mean I i k ∨
      (k ≤ j ∧ I.weight k / mean I i k = I.weight j / mean I i j) := by
  classical
  unfold high
  simp

theorem mem_low (I : StochasticInstance M n Ω) (j : Fin n) (i : M) (k : Fin n) :
    k ∈ low I j i ↔ k ∉ high I j i := by
  classical
  unfold low
  simp

theorem high_iff_low (I : StochasticInstance M n Ω) (i : M) (j k : Fin n) (hjk : j ≠ k) :
    k ∈ high I j i ↔ j ∈ low I k i := by
  rw [mem_low, mem_high, mem_high]
  set a := I.weight j / mean I i j
  set b := I.weight k / mean I i k
  have hne : j < k ∨ k < j := lt_or_gt_of_ne hjk
  constructor
  · rintro (h | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩)
    · linarith
    · linarith
    · linarith
    · rcases hne with h | h
      · exact absurd h1 (not_le.mpr h)
      · exact absurd h1' (not_le.mpr h)
  · intro h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    rcases lt_or_eq_of_le h1 with h3 | h3
    · left; exact h3
    · right
      refine ⟨?_, h3.symm⟩
      by_contra hkj
      push_neg at hkj
      exact h2 hkj.le h3

theorem sum_nat {s : Finset (Fin n)} {f : Fin n → ℝ} (h : ∀ l ∈ s, ∃ q : ℕ, f l = q) :
    ∃ Q : ℕ, ∑ l ∈ s, f l = Q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨Q, hQ⟩ := ih fun l hl => h l (Finset.mem_insert_of_mem hl)
    obtain ⟨q, hq⟩ := h a (Finset.mem_insert_self _ _)
    exact ⟨q + Q, by rw [Finset.sum_insert ha, hq, hQ]; push_cast; ring⟩

end Aux_GreedWorks_lemma_4

open GreedWorks.OnlineList Aux_GreedWorks_lemma_4 in
theorem solution {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m) :
    algorithmCost I m = ∑ j : Fin n, alpha I m j ∧
      ((∀ i j, I.eligible i j → ∃ q : ℕ, mean I i j = q) →
        algorithmCost I m = ∑ i : M, ∑' s : ℕ, beta I m i s) := by
  classical
  haveI := I.probability
  set w := I.weight with hw
  set C := nominalCompletion I m with hCdef
  set H : Fin n → Finset (Fin n) := fun j =>
    Finset.univ.filter fun k => m k = m j ∧ k ∈ high I j (m j) with hH
  have hCj : ∀ j, C j = ∑ k ∈ H j, mean I (m j) k := fun j => by
    simp only [hCdef, hH, nominalCompletion]
  -- integrability
  have hint : ∀ j k, m k = m j → Integrable (fun ω => (I.P (m j) k ω : ℝ)) I.Pr := by
    intro j k hk
    have he : I.eligible (m j) k := hk ▸ (hm k).1
    exact (I.memLp _ _ he).integrable one_le_two
  have hcost : algorithmCost I m = ∑ j, w j * C j := by
    unfold algorithmCost algorithmCompletion
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_finsetSum]
      · rw [hCj]
        rfl
      · intro k hk
        exact hint j k (Finset.mem_filter.mp hk).2.1
    · intro j _
      refine Integrable.const_mul ?_ _
      exact integrable_finsetSum _ fun k hk => hint j k (Finset.mem_filter.mp hk).2.1
  refine ⟨?_, ?_⟩
  · rw [hcost]
    -- split H j into k = j, k < j, k > j
    have hjH : ∀ j, j ∈ H j := fun j =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, (mem_high I j (m j) j).mpr (Or.inr ⟨le_rfl, rfl⟩)⟩
    have hsplit : ∀ j, C j = mean I (m j) j +
        ∑ k, (if k < j ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) +
        ∑ k, (if j < k ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) := by
      intro j
      rw [hCj, Finset.sum_filter]
      have : ∀ k, (if m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) =
          (if k = j then mean I (m j) k else 0) +
          (if k < j ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) +
          (if j < k ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) := by
        intro k
        rcases lt_trichotomy k j with h | h | h
        · simp [h, ne_of_lt h, not_lt_of_gt h]
        · subst h
          have := (Finset.mem_filter.mp (hjH k)).2
          simp [this]
        · simp [h, ne_of_gt h, not_lt_of_gt h]
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq']
      simp
    have halpha : ∀ j, alpha I m j = w j * mean I (m j) j +
        w j * ∑ k, (if k < j ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) +
        mean I (m j) j * ∑ k, (if k < j ∧ m k = m j ∧ k ∈ low I j (m j) then w k else 0) := by
      intro j
      unfold alpha incrementalCost
      rw [Finset.sum_filter, Finset.sum_filter]
      ring
    -- double counting
    have hdc : ∑ j, w j * ∑ k, (if j < k ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0)
        = ∑ j, mean I (m j) j * ∑ k, (if k < j ∧ m k = m j ∧ k ∈ low I j (m j) then w k else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm (f := fun j k => mean I (m j) j *
        (if k < j ∧ m k = m j ∧ k ∈ low I j (m j) then w k else 0))]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases hjk : j < k
      · by_cases hmk : m k = m j
        · have hiff := high_iff_low I (m j) j k (ne_of_lt hjk)
          by_cases hh : k ∈ high I j (m j)
          · rw [if_pos ⟨hjk, hmk, hh⟩, if_pos ⟨hjk, hmk.symm, by rw [hmk]; exact hiff.mp hh⟩, hmk]
            ring
          · rw [if_neg (fun h => hh h.2.2),
              if_neg (fun h => hh (hiff.mpr (by rw [← hmk]; exact h.2.2)))]
            ring
        · rw [if_neg (fun h => hmk h.2.1), if_neg (fun h => hmk h.2.1.symm)]
          ring
      · rw [if_neg (fun h => hjk h.1), if_neg (fun h => hjk h.1)]
        ring
    simp only [halpha, hsplit]
    have e : ∀ j, w j * (mean I (m j) j +
        ∑ k, (if k < j ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) +
        ∑ k, (if j < k ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0)) =
        w j * mean I (m j) j +
        w j * ∑ k, (if k < j ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) +
        w j * ∑ k, (if j < k ∧ m k = m j ∧ k ∈ high I j (m j) then mean I (m j) k else 0) :=
      fun j => by ring
    simp only [e, Finset.sum_add_distrib, hdc]
  · intro hq
    -- C k is a natural number
    have hCnat : ∀ k, ∃ Q : ℕ, C k = Q := by
      intro k
      rw [hCj]
      apply sum_nat
      intro l hl
      have hml := (Finset.mem_filter.mp hl).2.1
      have he : I.eligible (m k) l := hml ▸ (hm l).1
      exact hq _ _ he
    choose Q hQ using hCnat
    set S := ∑ k, Q k + 1 with hS
    have hQS : ∀ k, Q k < S := by
      intro k
      have := Finset.single_le_sum (f := Q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    have hbeta : ∀ i s, beta I m i s = ∑ k, (if m k = i ∧ s < Q k then w k else 0) := by
      intro i s
      unfold beta
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hCdef, hQ k]
      simp only [Nat.cast_lt]
      rfl
    have htsum : ∀ i, ∑' s : ℕ, beta I m i s = ∑ k, (if m k = i then w k * Q k else 0) := by
      intro i
      rw [tsum_eq_sum (s := Finset.range S)]
      · simp only [hbeta]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : m k = i
        · simp only [hk, true_and, if_true]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          have : (Finset.range S).filter (fun s => s < Q k) = Finset.range (Q k) := by
            ext s; simp only [Finset.mem_filter, Finset.mem_range]
            constructor
            · intro h; exact h.2
            · intro h; exact ⟨lt_trans h (hQS k), h⟩
          rw [this, Finset.card_range]; ring
        · simp [hk]
      · intro s hs
        rw [hbeta]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg]
        rintro ⟨-, h⟩
        rw [Finset.mem_range] at hs
        exact hs (lt_trans h (hQS k))
    simp only [htsum]
    rw [hcost, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq, hQ k]
    simp
