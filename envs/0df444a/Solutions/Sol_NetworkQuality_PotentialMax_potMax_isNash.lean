-- Prove2me | solution 1 for NetworkQuality.PotentialMax.potMax_isNash
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:23:16.170991+00:00
-- url     : https://prove2.me/submissions/caf8d551-7171-43c6-95f4-70dce73a7016

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

set_option autoImplicit false
open NetworkQuality.PotentialMax Market

theorem solution {n : ℕ} (M : Market n) (hM : M.Standing) (B : Finset (Fin n)) (p q : ℝ)
    (hB : M.IsPotMax B p q) : M.IsNash B p q := by
  have hv : ∀ i, 0 < M.v i := hM.2.1
  constructor
  · intro i hi
    have h := hB (B.erase i)
    have hc : (B.erase i).card + 1 = B.card := Finset.card_erase_add_one hi
    have hs : ∑ k ∈ Finset.range B.card, M.f (k + 1) q
        = ∑ k ∈ Finset.range (B.erase i).card, M.f (k + 1) q + M.f B.card q := by
      rw [← hc, Finset.sum_range_succ, hc]
    have hs2 : ∑ k ∈ B, 1 / M.v k = 1 / M.v i + ∑ k ∈ B.erase i, 1 / M.v k :=
      (Finset.add_sum_erase B (fun k => 1 / M.v k) hi).symm
    simp only [pot] at h
    rw [hs, hs2] at h
    have hnot : i ∉ B.erase i := Finset.notMem_erase i B
    simp only [u, hnot, hi, if_false, if_true]
    have h3 : 0 ≤ M.f B.card q - p * (1 / M.v i) := by nlinarith
    have h4 : p * (1 / M.v i) * M.v i = p := by have := (hv i).ne'; field_simp
    nlinarith [hv i]
  · intro i hi
    have h := hB (insert i B)
    have hc : (insert i B).card = B.card + 1 := Finset.card_insert_of_notMem hi
    have hs : ∑ k ∈ Finset.range (insert i B).card, M.f (k + 1) q
        = ∑ k ∈ Finset.range B.card, M.f (k + 1) q + M.f (B.card + 1) q := by
      rw [hc, Finset.sum_range_succ]
    have hs2 : ∑ k ∈ insert i B, 1 / M.v k = 1 / M.v i + ∑ k ∈ B, 1 / M.v k :=
      Finset.sum_insert hi
    simp only [pot] at h
    rw [hs, hs2] at h
    simp only [u, hi, Finset.mem_insert, true_or, if_false, if_true, hc]
    have h3 : M.f (B.card + 1) q - p * (1 / M.v i) ≤ 0 := by nlinarith
    have h4 : p * (1 / M.v i) * M.v i = p := by have := (hv i).ne'; field_simp
    nlinarith [hv i]
