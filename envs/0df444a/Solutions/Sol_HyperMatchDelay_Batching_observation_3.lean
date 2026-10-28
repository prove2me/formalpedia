-- Prove2me | solution 1 for HyperMatchDelay.Batching.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:07:29.21774+00:00
-- url     : https://prove2.me/submissions/c1bf2cbd-aadc-4c36-9a6b-c9ec4d5e3399

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

open HyperMatchDelay.Batching in
theorem solution (n d k z : ℕ) (i : ℤ) (e : Finset ℕ)
    (he : e ⊆ window n d z i) (hne : e.Nonempty) (hlong : (d : ℤ) - k < (diam e : ℤ)) :
    (e ∩ firstK (window n d z i) k).Nonempty ∧
    (e ∩ lastK (window n d z i) k).Nonempty := by
  have hW : ∀ v, v ∈ window n d z i ↔
      v ∈ Finset.Icc 1 n ∧ (z:ℤ) + i * d ≤ v ∧ (v:ℤ) ≤ (z:ℤ) + i * d + d - 1 := by
    intro v
    unfold window
    rw [Finset.mem_filter]
    have e1 : (z:ℤ) + (i + 1) * d - 1 = (z:ℤ) + i * d + d - 1 := by ring
    rw [e1]
  set t : ℤ := (z:ℤ) + i * d with ht
  set W := window n d z i with hWdef
  set m := e.min' hne with hm
  set M := e.max' hne with hM
  have hmin : m ∈ e := e.min'_mem hne
  have hmax : M ∈ e := e.max'_mem hne
  have hmM : m ≤ M := Finset.min'_le e M hmax
  have hdiam : diam e = M - m := by unfold diam; rw [dif_pos hne]
  rw [hdiam] at hlong
  have hmW := (hW m).1 (he hmin)
  have hMW := (hW M).1 (he hmax)
  have hD : ((M - m : ℕ) : ℤ) = (M : ℤ) - m := by push_cast [Nat.cast_sub hmM]; ring
  constructor
  · refine ⟨m, Finset.mem_inter.2 ⟨hmin, ?_⟩⟩
    unfold firstK
    rw [Finset.mem_filter]
    refine ⟨he hmin, ?_⟩
    set a := t.toNat with ha
    have ha1 : t ≤ (a : ℤ) := Int.self_le_toNat t
    have hsub : W.filter (fun u => u < m) ⊆ Finset.Ico a m := by
      intro u hu
      rw [Finset.mem_filter] at hu
      have huW := (hW u).1 hu.1
      rw [Finset.mem_Ico]
      exact ⟨Int.toNat_le.2 huW.2.1, hu.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have : m - a < k := by omega
    omega
  · refine ⟨M, Finset.mem_inter.2 ⟨hmax, ?_⟩⟩
    unfold lastK
    rw [Finset.mem_filter]
    refine ⟨he hmax, ?_⟩
    have hb0 : 0 ≤ t + d - 1 := by omega
    obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = t + d - 1 := ⟨(t + d - 1).toNat, Int.toNat_of_nonneg hb0⟩
    have hsub : W.filter (fun u => M < u) ⊆ Finset.Ioc M b := by
      intro u hu
      rw [Finset.mem_filter] at hu
      have huW := (hW u).1 hu.1
      rw [Finset.mem_Ioc]
      exact ⟨hu.2, by omega⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hcard
    have : b - M < k := by omega
    omega
