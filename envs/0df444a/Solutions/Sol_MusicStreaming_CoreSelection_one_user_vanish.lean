-- Prove2me | solution 1 for MusicStreaming.CoreSelection.one_user_vanish
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:14.096049+00:00
-- url     : https://prove2.me/submissions/05eb25fe-9bd7-47bb-a5ed-4d193edf805c

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

set_option autoImplicit false

open MusicStreaming.CoreSelection

namespace MS3V

open MusicStreaming.Axioms in
lemma listened_single (j : ℕ) {n : ℕ} (x : Fin n → ℕ) :
    listened (Finsupp.single j x) j = Finset.univ.filter (fun i => 0 < x i) := by
  simp [listened]

lemma pstar_single {n : ℕ} (j : ℕ) (x : Fin n → ℕ)
    (h : Finset.univ.filter (fun i => 0 < x i) ≠ Finset.univ) :
    InPStar (Finsupp.single j x) := by
  intro j' hj'
  have : j' = j := by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp hj') (by simp [Finsupp.single_apply, Ne.symm hne])
  subst this
  rw [listened_single]; exact h

lemma pstar_single_iff {n : ℕ} (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0)
    (h : InPStar (Finsupp.single j x)) :
    Finset.univ.filter (fun i => 0 < x i) ≠ Finset.univ := by
  have hj : j ∈ (Finsupp.single j x).support := by simp [hx]
  have := h j hj
  rwa [listened_single] at this

/-- Display (1). -/
theorem vanish_aux (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I)
    (hC : CoreSelectionOn I)
    (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0) (hP : InPStar (Finsupp.single j x))
    (i : Fin n) (hi : x i = 0) :
    I (Finsupp.single j x) i = 0 := by
  set t : MusicStreaming.Axioms.Problem n := Finsupp.single j x with ht
  have hsupp : t.support = {j} := Finsupp.support_single_ne_zero j hx
  have ht0 : t ≠ 0 := by simp [t, hx]
  obtain ⟨hnn, hpos⟩ := hI t hP ht0
  set L := Finset.univ.filter (fun i => 0 < x i) with hL
  have hcore := (hC t hP).2 L (Finset.subset_univ _)
  have hgame : MusicStreaming.Core.game t L = 1 := by
    unfold MusicStreaming.Core.game
    rw [hsupp]
    have : MusicStreaming.Axioms.listened t j ⊆ L := by rw [ht, listened_single]
    simp [Finset.filter_singleton, this]
  have hrew : ∀ k, MusicStreaming.Axioms.reward I t k = I t k / ∑ i', I t i' := by
    intro k; simp [MusicStreaming.Axioms.reward, hsupp]
  rw [hgame] at hcore
  simp only [hrew] at hcore
  rw [← Finset.sum_div, le_div_iff₀ hpos, one_mul] at hcore
  have hsplit := Finset.sum_add_sum_compl L (I t)
  have hcompl : ∑ k ∈ Lᶜ, I t k ≤ 0 := by linarith
  have hiL : i ∈ Lᶜ := by simp [L, hi]
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn k)).mp
    (le_antisymm hcompl (Finset.sum_nonneg fun k _ => hnn k)) i hiL

end MS3V

theorem solution (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hC : CoreSelectionOn I)
    (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0) (hP : InPStar (Finsupp.single j x))
    (i : Fin n) (hi : x i = 0) :
    I (Finsupp.single j x) i = 0 :=
  MS3V.vanish_aux n I hI hC j x hx hP i hi
