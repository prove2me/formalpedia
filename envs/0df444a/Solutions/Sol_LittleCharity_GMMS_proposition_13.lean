-- Prove2me | solution 1 for LittleCharity.GMMS.proposition_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:43:12.247229+00:00
-- url     : https://prove2.me/submissions/9955cbde-575f-4648-8259-53d0ed19d63d

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false
open LittleCharity.MMS

theorem lcm_add_mono {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    {A B : Finset (Fin m)} (h : A ⊆ B) : v i A ≤ v i B := by
  rw [hadd.1 i A, hadd.1 i B]
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hadd.2 i {g})

theorem lcm_mms_step {m : ℕ} (w : Finset (Fin m) → ℝ) (hw : ∀ A B, A ⊆ B → w A ≤ w B)
    (k : ℕ) (hk : 1 ≤ k) (S S' : Finset (Fin m)) (hS : S' ⊆ S) (hc : (S \ S').card ≤ 1) :
    mms w (k + 1) S ≤ mms w k S' := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold mms
  apply ciSup_le
  intro f
  obtain ⟨a, ha⟩ : ∃ a : Fin (k' + 1 + 1), ∀ x ∈ S \ S', f x = a := by
    by_cases h : (S \ S').Nonempty
    · obtain ⟨x0, hx0⟩ := h
      refine ⟨f x0, fun x hx => ?_⟩
      rw [Finset.card_le_one.mp hc x hx x0 hx0]
    · exact ⟨0, fun x hx => absurd ⟨x, hx⟩ h⟩
  let f' : Fin m → Fin (k' + 1) := fun x =>
    if h : f x = a then 0 else Classical.choose (Fin.exists_succAbove_eq h)
  have hf' : ∀ x, f x ≠ a → a.succAbove (f' x) = f x := by
    intro x hx
    simp only [f', dif_neg hx]
    exact Classical.choose_spec (Fin.exists_succAbove_eq hx)
  refine le_trans ?_ (le_ciSup (f := fun g : Fin m → Fin (k' + 1) =>
    ⨅ j : Fin (k' + 1), w (S'.filter (fun x => g x = j))) (Set.finite_range _).bddAbove f')
  refine le_ciInf (fun j => ?_)
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow (a.succAbove j)) (hw _ _ ?_)
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  obtain ⟨hxS, hxf⟩ := hx
  have hxa : f x ≠ a := by rw [hxf]; exact Fin.succAbove_ne a j
  have hxS' : x ∈ S' := by
    by_contra hn
    exact hxa (ha x (Finset.mem_sdiff.mpr ⟨hxS, hn⟩))
  refine ⟨hxS', ?_⟩
  apply Fin.succAbove_right_injective (p := a)
  rw [hf' x hxa, hxf]

theorem lcm_mms_remove {m : ℕ} (w : Finset (Fin m) → ℝ) (hw : ∀ A B, A ⊆ B → w A ≤ w B) :
    ∀ (d k : ℕ), 1 ≤ k → ∀ S S' : Finset (Fin m), S' ⊆ S → (S \ S').card ≤ d →
      mms w (k + d) S ≤ mms w k S' := by
  classical
  intro d
  induction d with
  | zero =>
    intro k hk S S' hS hc
    have h0 : S \ S' = ∅ := Finset.card_eq_zero.mp (by omega)
    have : S = S' := by
      apply Finset.Subset.antisymm _ hS
      intro x hx
      by_contra hn
      have : x ∈ S \ S' := Finset.mem_sdiff.mpr ⟨hx, hn⟩
      rw [h0] at this; simp at this
    subst this
    simp
  | succ d ih =>
    intro k hk S S' hS hc
    by_cases hne : (S \ S').Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [Finset.mem_sdiff] at hg
      have hS1 : S' ⊆ S.erase g := by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨fun h => hg.2 (h ▸ hx), hS hx⟩
      have hc1 : ((S.erase g) \ S').card ≤ d := by
        have : (S.erase g) \ S' = (S \ S').erase g := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
        rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr hg)]
        omega
      have h1 := ih k hk (S.erase g) S' hS1 hc1
      have h2 := lcm_mms_step w hw (k + d) (by omega) S (S.erase g) (Finset.erase_subset _ _) (by
        calc (S \ S.erase g).card ≤ ({g} : Finset (Fin m)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_erase] at hx
              simp only [Finset.mem_singleton]
              by_contra hne; exact hx.2 ⟨hne, hx.1⟩
          _ = 1 := Finset.card_singleton g)
      exact le_trans h2 h1
    · have h0 : S \ S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have : S = S' := by
        apply Finset.Subset.antisymm _ hS
        intro x hx
        by_contra hn
        have : x ∈ S \ S' := Finset.mem_sdiff.mpr ⟨hx, hn⟩
        rw [h0] at this; simp at this
      subst this
      have h1 := ih k hk S S (Finset.Subset.refl _) (by simp)
      have h2 := lcm_mms_step w hw (k + d) (by omega) S S (Finset.Subset.refl _) (by simp)
      exact le_trans h2 h1

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (N N' : Finset (Fin n)) (M M' : Finset (Fin m)) (hN : N' ⊆ N) (hM : M' ⊆ M)
    (hcard : (M \ M').card ≤ (N \ N').card) (i : Fin n) (hi : i ∈ N') :
    mms (v i) N.card M ≤ mms (v i) N'.card M' := by
  have hpos : 1 ≤ N'.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hsum : N.card = N'.card + (N \ N').card := by
    have := Finset.card_sdiff_add_card_eq_card hN
    omega
  rw [hsum]
  exact lcm_mms_remove (v i) (fun A B h => lcm_add_mono hadd i h) _ _ hpos M M' hM hcard
