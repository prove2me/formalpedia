-- Prove2me | solution 1 for Kyprianou.Ch05.renewalCrossingCellIffIndexV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:04:02.106919+00:00
-- url     : https://prove2.me/submissions/dc9bb76f-9d43-4348-bf4e-cf245baf17e3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem solution
    {Omega : Type} (Z : ℕ → Omega → ℝ) (w : Omega)
    (hm : Monotone (fun n => renewalEpoch Z n w))
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA2 : A ⊆ Ioi 0) (n : ℕ) :
    (renewalEpoch Z n w ∈ Icc 0 x ∧
      Z n w - (x-renewalEpoch Z n w) ∈ A ∧ x-renewalEpoch Z n w ∈ B) ↔
    (nextRenewalIndex Z x w = n+1 ∧ 0 < renewalOvershoot Z x w ∧
      renewalOvershoot Z x w ∈ A ∧ renewalUndershoot Z x w ∈ B) := by
  let S := fun k => renewalEpoch Z k w
  let H : Set ℕ := {k | 0 < k ∧ x < S k}
  have hS0 : S 0 = 0 := by simp [S,renewalEpoch]
  have hS (k : ℕ) : S (k+1) = S k + Z k w := by simp [S,renewalEpoch,Finset.sum_range_succ]
  have hN : nextRenewalIndex Z x w = sInf H := rfl
  have hOver (hi : nextRenewalIndex Z x w = n+1) :
      renewalOvershoot Z x w = Z n w - (x-S n) := by
    unfold renewalOvershoot
    rw [hi]
    change S (n+1)-x = _
    rw [hS]; ring
  constructor
  · rintro ⟨hv,ha,hb⟩
    have hp : 0 < Z n w - (x-S n) := hA2 ha
    have hn : n+1 ∈ H := ⟨Nat.succ_pos n,by rw [hS]; linarith⟩
    have hmem := Nat.sInf_mem ⟨n+1,hn⟩
    have hle := Nat.sInf_le hn
    have he : sInf H = n+1 := by
      by_contra hne
      exact (not_lt_of_ge ((hm (show sInf H ≤ n by omega)).trans hv.2)) hmem.2
    have hi := hN.trans he
    refine ⟨hi,?_,?_,?_⟩
    · rwa [hOver hi]
    · rwa [hOver hi]
    · simpa [renewalUndershoot,hi,S] using hb
  · rintro ⟨hi,ho,ha,hb⟩
    have hv0 : 0 ≤ S n := by rw [← hS0]; exact hm (Nat.zero_le n)
    have hvx : S n ≤ x := by
      by_contra! hv
      have hn : 0 < n := Nat.pos_of_ne_zero (fun he => by rw [he,hS0] at hv; linarith)
      have hle := Nat.sInf_le (show n ∈ H from ⟨hn,hv⟩)
      rw [← hN,hi] at hle
      omega
    refine ⟨⟨hv0,hvx⟩,?_,?_⟩
    · rwa [← hOver hi]
    · simpa [renewalUndershoot,hi,S] using hb
