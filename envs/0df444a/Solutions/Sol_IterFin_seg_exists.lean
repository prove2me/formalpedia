-- Prove2me | solution 1 for IterFin_seg_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:14.391257+00:00
-- url     : https://prove2.me/submissions/bacdaa3e-51a8-40c6-851c-8ffdb5bc8959

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} {m : ℕ} {al : List A} (h : al ∈ L ^ m) :
    ∃ n ≤ m, ∃ φ : Stream' ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
      ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L := by
  change ∃ n ≤ m, ∃ φ : ℕ → ℕ, StrictMonoOn φ {k | k < n + 1} ∧ φ 0 = 0 ∧ φ n = al.length ∧
    ∀ k < n, al.extract (φ k) (φ (k + 1)) ∈ L
  change al ∈ IterFin L m at h
  induction' m with m h_ind generalizing al <;> simp [IterFin] at h
  · use 0 ; simp ; use (fun _ ↦ 0) ; simp [h]
  obtain ⟨al0, al1, h_al0, h_al1, rfl⟩ := h
  obtain ⟨n, h_n, φ, h_mono, h_init, h_last, h_seg⟩ := h_ind h_al0
  rcases Classical.em (al1 = []) with ⟨rfl⟩ | h_al1'
  . refine ⟨n, by omega, φ, ?_⟩
    simpa using And.intro h_mono (And.intro h_init (And.intro h_last h_seg))
  have := List.ne_nil_iff_length_pos.mp h_al1'
  use (n + 1) ; simp [(show n + 1 ≤ m + 1 by omega), -List.extract_eq_drop_take]
  use (fun k ↦ if k < n + 1 then φ k else al0.length + al1.length)
  simp [h_init, -List.extract_eq_drop_take, -Nat.lt_succ_iff] ; constructor
  · intro i h_i j h_j h_ij ; simp at h_i h_j
    rcases (show (i < n + 1 ∧ j < n + 1) ∨ (i < n + 1 ∧ j = n + 1) by omega)
      with ⟨h_i', h_j'⟩ | ⟨h_i', h_j'⟩ <;> simp [h_i', h_j']
    · simpa [show i ≤ n by omega, show j ≤ n by omega] using h_mono h_i' h_j' h_ij
    · have := StrictMonoOn.monotoneOn h_mono h_i' (show n < n + 1 by omega) (show i ≤ n by omega)
      simp only [if_pos (show i ≤ n by omega)]
      omega
  · intro k h_k ; rcases (show k < n ∨ n = k by omega) with h_k' | ⟨rfl⟩
    · suffices h1 : (al0 ++ al1).extract (φ k) (φ (k + 1)) = al0.extract (φ k) (φ (k + 1)) by
        simp [h_k, h_k', h1, h_seg, -List.extract_eq_drop_take]
      have : φ k < φ (k + 1) := h_mono (show k < n + 1 by omega) (show k + 1 < n + 1 by omega) (by omega)
      have h1 : φ k + (φ (k + 1) - φ k) = φ (k + 1) := by omega
      have h2 : φ (k + 1) ≤ al0.length := by
        have := StrictMonoOn.monotoneOn h_mono (show k + 1 < n + 1 by omega) (show n < n + 1 by omega) (by omega)
        simpa [← h_last]
      simp only [List.extract_eq_drop_take, List.take_drop, h1, List.take_append_of_le_length h2]
    · simp [h_last, h_al1]
