-- Prove2me | solution 1 for InterdepSOS.RSV.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T14:19:12.103969+00:00
-- url     : https://prove2.me/submissions/039c1303-ee39-46f3-b1e1-db91d731b837

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting
import Theorems.Thm_InterdepSOS_RSV_proposition_2_1
import Theorems.Thm_InterdepSOS_RSV_rsv_monotone
import Theorems.Thm_InterdepSOS_RSV_display_4

open InterdepSOS.RSV

theorem solution {n : ℕ} (I : Set (Finset (Fin n)))
    (hI : IsDownwardClosed I) (v : Valuation n) (hv : IsValuation v)
    (d : ℝ) (hd : ∀ i, IsDSOS d (v i))
    (sel : Finset (Fin n) → Allocation n) (hsel : IsRSVSelector I v sel) :
    (∀ B, ∃ p : Payment n,
      IsExPostIC v (sel B) p ∧ IsExPostIR v (sel B) p) ∧
    ∀ s, ∀ S ∈ I,
      (∑ i ∈ S, v i s) ≤
        2 * (d + 1) * avgB (fun B => ∑ i ∈ sel B s, v i s) := by
  refine ⟨fun B => (proposition_2_1 v hv (sel B)).2 (rsv_monotone I v hv sel hsel B), ?_⟩
  intro s S hS
  rcases S.eq_empty_or_nonempty with hSe | ⟨i0, hi0⟩
  · subst hSe
    simp only [Finset.sum_empty]
    -- need 0 ≤ 2(d+1) avgB ...; if Fin n is empty everything is zero
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · have : avgB (fun B => ∑ i ∈ sel B s, v i s) = 0 := by
        unfold avgB
        rw [Finset.sum_eq_zero (fun B _ => by rw [Finset.eq_empty_of_isEmpty (sel B s)]; simp)]
        simp
      rw [this]; simp
    · have hd1 : 1 ≤ d := by
        have h := hd i i 0 1 s s (fun _ _ => le_rfl)
        have hlt := hv.2.2 i s 0 1 zero_lt_one
        simp only [zero_add] at h
        nlinarith
      apply mul_nonneg (by linarith)
      unfold avgB
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun B _ => Finset.sum_nonneg (fun j _ => hv.1 j s))
  · have hd1 : 1 ≤ d := by
      have h := hd i0 i0 0 1 s s (fun _ _ => le_rfl)
      have hlt := hv.2.2 i0 s 0 1 zero_lt_one
      simp only [zero_add] at h
      nlinarith
    have hpos : 0 < d + 1 := by linarith
    -- pointwise bound for each B
    have hB : ∀ B : Finset (Fin n),
        ∑ i ∈ S, (if i ∈ B then rsvWeight v B s i else 0) ≤ ∑ i ∈ sel B s, v i s := by
      intro B
      obtain ⟨_, _, hmax⟩ := hsel B s
      have hSB : S ∩ B ∈ I := hI S hS _ Finset.inter_subset_left
      have h1 := hmax (S ∩ B) hSB Finset.inter_subset_right
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
      refine h1.trans (Finset.sum_le_sum fun j _ => ?_)
      unfold rsvWeight
      apply hv.2.1 j
      intro l
      unfold keepOn
      split_ifs <;> simp
    have havg : ∑ i ∈ S, avgB (fun B => if i ∈ B then rsvWeight v B s i else 0) ≤
        avgB (fun B => ∑ i ∈ sel B s, v i s) := by
      unfold avgB
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun B _ => hB B
    have h4 : ∑ i ∈ S, v i s / (d + 1) * (1 / 2 : ℝ) ≤
        avgB (fun B => ∑ i ∈ sel B s, v i s) :=
      (Finset.sum_le_sum fun i _ => display_4 v hv d hd i s).trans havg
    rw [← Finset.sum_mul, ← Finset.sum_div] at h4
    have : (∑ i ∈ S, v i s) = 2 * (d + 1) * ((∑ i ∈ S, v i s) / (d + 1) * (1 / 2)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h4 (by linarith)
