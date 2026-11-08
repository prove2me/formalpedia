-- Prove2me | solution 1 for NestedLogitNBR.lemma14_terms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:59:15.205782+00:00
-- url     : https://prove2.me/submissions/2e7a7627-2119-41a3-8bdb-c49567e720af

import Mathlib
import Definitions.Def_NestedLogitNBR_prefWeight
import Definitions.Def_NestedLogitNBR_nbr
import Definitions.Def_NestedLogitNBR_nestRevenue

open NestedLogitNBR in
theorem solution {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (hord : Antitone (r i)) (hγ : 1 < γ i)
    (k : Fin n) (hq : 0 < prefWeight v i (nbr k.val))
    (hR : 0 < nestRevenue r v i (nbr (k.val + 1))) :
    1 ≤ nestRevenue r v i (nbr k.val) / nestRevenue r v i (nbr (k.val + 1)) ∧
      1 ≤ nestRevenue r v i (nbr (k.val + 1)) / nestRevenue r v i (nbr k.val) *
        (prefWeight v i (nbr (k.val + 1)) ^ γ i / prefWeight v i (nbr k.val) ^ γ i) := by
  have hins : (nbr (k.val + 1) : Finset (Fin n)) = insert k (nbr k.val) := by
    ext j
    simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [Fin.ext_iff]
    constructor <;> intro h <;> omega
  have hnot : k ∉ (nbr k.val : Finset (Fin n)) := by
    simp [nbr]
  have hW'eq : prefWeight v i (nbr (k.val + 1)) = v i k + prefWeight v i (nbr k.val) := by
    unfold prefWeight; rw [hins, Finset.sum_insert hnot]
  have hN'eq : (∑ j ∈ nbr (k.val + 1), r i j * v i j) =
      r i k * v i k + ∑ j ∈ nbr k.val, r i j * v i j := by
    rw [hins, Finset.sum_insert hnot]
  have hNge : r i k * prefWeight v i (nbr k.val) ≤ ∑ j ∈ nbr k.val, r i j * v i j := by
    unfold prefWeight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := by
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Fin.le_iff_val_le_val.mpr hj.le
    exact mul_le_mul_of_nonneg_right (hord hjk) (hv j)
  have hRdef : nestRevenue r v i (nbr k.val) =
      (∑ j ∈ nbr k.val, r i j * v i j) / prefWeight v i (nbr k.val) := rfl
  have hR'def : nestRevenue r v i (nbr (k.val + 1)) =
      (∑ j ∈ nbr (k.val + 1), r i j * v i j) / prefWeight v i (nbr (k.val + 1)) := rfl
  rw [hRdef, hR'def]
  rw [hR'def] at hR
  rw [hW'eq, hN'eq]
  rw [hW'eq, hN'eq] at hR
  obtain ⟨W, hWd⟩ : ∃ W, W = prefWeight v i (nbr k.val) := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N, N = ∑ j ∈ nbr k.val, r i j * v i j := ⟨_, rfl⟩
  rw [← hWd, ← hNd]
  rw [← hWd, ← hNd] at hR
  rw [← hWd] at hq
  rw [← hWd, ← hNd] at hNge
  have hvk := hv k
  have hrk := hr k
  have hW'pos : 0 < v i k + W := by linarith
  have hN'pos : 0 < r i k * v i k + N := by
    have := hR
    rw [lt_div_iff₀ hW'pos, zero_mul] at this
    exact this
  have hNpos : 0 < N := by
    by_contra hcon
    push_neg at hcon
    have h1 : r i k * W ≤ 0 := hNge.trans hcon
    have h2 : r i k = 0 := by
      rcases hrk.lt_or_eq with h | h
      · exact absurd h1 (not_le.mpr (mul_pos h hq))
      · exact h.symm
    rw [h2] at hN'pos
    linarith
  have hRpos : 0 < N / W := div_pos hNpos hq
  refine ⟨?_, ?_⟩
  · rw [one_le_div hR, div_le_div_iff₀ hW'pos hq]
    nlinarith [mul_le_mul_of_nonneg_right hNge hvk]
  · have hx1 : 1 ≤ (v i k + W) / W := by
      rw [one_le_div hq]; linarith
    have hxγ : (v i k + W) / W ≤ ((v i k + W) / W) ^ γ i := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 hγ.le
      rwa [Real.rpow_one] at this
    rw [← Real.div_rpow hW'pos.le hq.le]
    have hkey : (r i k * v i k + N) / (v i k + W) / (N / W) * ((v i k + W) / W) =
        (r i k * v i k + N) / N := by
      have := hW'pos.ne'
      have := hNpos.ne'
      have := hq.ne'
      field_simp <;> ring
    have hge1 : 1 ≤ (r i k * v i k + N) / N := by
      rw [one_le_div hNpos]; nlinarith [mul_nonneg hrk hvk]
    have hnn : 0 ≤ (r i k * v i k + N) / (v i k + W) / (N / W) :=
      div_nonneg (div_nonneg hN'pos.le hW'pos.le) hRpos.le
    calc (1 : ℝ) ≤ (r i k * v i k + N) / N := hge1
      _ = (r i k * v i k + N) / (v i k + W) / (N / W) * ((v i k + W) / W) := hkey.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hxγ hnn
