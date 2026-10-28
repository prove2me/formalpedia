-- Prove2me | solution 1 for MusicStreaming.CoreSelection.claim
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:04:12.564614+00:00
-- url     : https://prove2.me/submissions/2a8761b7-8fd8-49e9-b273-dca2c38d4585

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting
import Theorems.Thm_MusicStreaming_CoreSelection_one_user_vanish

set_option autoImplicit false

open MusicStreaming.CoreSelection

namespace MS3C

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

lemma pstar_add {n : ℕ} (t₁ t₂ : MusicStreaming.Axioms.Problem n)
    (h₁ : InPStar t₁) (h₂ : InPStar t₂) (hd : Disjoint t₁.support t₂.support) :
    InPStar (t₁ + t₂) := by
  intro j hj
  rcases Finset.mem_union.mp (Finsupp.support_add hj) with h | h
  · have h2 : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd h)
    have := h₁ j h
    simpa [MusicStreaming.Axioms.listened, h2] using this
  · have h1 : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd h)
    have := h₂ j h
    simpa [MusicStreaming.Axioms.listened, h1] using this

lemma pstar_of_add {n : ℕ} (t₁ t₂ : MusicStreaming.Axioms.Problem n)
    (h : InPStar (t₁ + t₂)) (hd : Disjoint t₁.support t₂.support) :
    InPStar t₁ ∧ InPStar t₂ := by
  constructor
  · intro j hj
    have h2 : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hj)
    have hj' : j ∈ (t₁ + t₂).support := by
      rw [Finsupp.mem_support_iff] at hj ⊢; simpa [h2] using hj
    have := h j hj'
    simpa [MusicStreaming.Axioms.listened, h2] using this
  · intro j hj
    have h1 : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd hj)
    have hj' : j ∈ (t₁ + t₂).support := by
      rw [Finsupp.mem_support_iff] at hj ⊢; simpa [h1] using hj
    have := h j hj'
    simpa [MusicStreaming.Axioms.listened, h1] using this

/-- One half of the Claim: `B ≤ A`. -/
lemma claim_half (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I)
    (hA : AdditivityOn I) (hC : CoreSelectionOn I) (j₁ j₂ : ℕ) (x y : Fin n → ℕ)
    (hj : j₁ ≠ j₂) (hx : x ≠ 0) (hy : y ≠ 0)
    (hPx : InPStar (Finsupp.single j₁ x)) (hPy : InPStar (Finsupp.single j₂ y))
    (hdisj : Disjoint (Finset.univ.filter (fun i => 0 < x i))
      (Finset.univ.filter (fun i => 0 < y i))) :
    ∑ i, I (Finsupp.single j₂ y) i ≤ ∑ i, I (Finsupp.single j₁ x) i := by
  set t₁ : MusicStreaming.Axioms.Problem n := Finsupp.single j₁ x with ht₁
  set t₂ : MusicStreaming.Axioms.Problem n := Finsupp.single j₂ y with ht₂
  have hs₁ : t₁.support = {j₁} := Finsupp.support_single_ne_zero j₁ hx
  have hs₂ : t₂.support = {j₂} := Finsupp.support_single_ne_zero j₂ hy
  have hd : Disjoint t₁.support t₂.support := by
    rw [hs₁, hs₂]; simpa using hj
  set t := t₁ + t₂ with ht
  have hP : InPStar t := pstar_add t₁ t₂ hPx hPy hd
  have hadd : I t = I t₁ + I t₂ := hA t₁ t₂ hPx hPy hd
  have ht0 : t ≠ 0 := by
    intro h0
    have : t j₁ = 0 := by rw [h0]; rfl
    simp [t, t₁, t₂, Finsupp.single_apply, hj] at this
    exact hx this
  obtain ⟨hnn, hpos⟩ := hI t hP ht0
  obtain ⟨hnn₁, hpos₁⟩ := hI t₁ hPx (by simp [t₁, hx])
  obtain ⟨hnn₂, hpos₂⟩ := hI t₂ hPy (by simp [t₂, hy])
  have hsupp : t.support = {j₁, j₂} := by
    rw [ht, Finsupp.support_add_eq hd, hs₁, hs₂]; rfl
  set L₁ := Finset.univ.filter (fun i => 0 < x i) with hL₁
  set L₂ := Finset.univ.filter (fun i => 0 < y i) with hL₂
  have htj₁ : t j₁ = x := by simp [t, t₁, t₂, Finsupp.single_apply, hj]
  have htj₂ : t j₂ = y := by simp [t, t₁, t₂, Finsupp.single_apply, hj]
  have hlis₁ : MusicStreaming.Axioms.listened t j₁ = L₁ := by
    simp [MusicStreaming.Axioms.listened, htj₁, L₁]
  have hlis₂ : MusicStreaming.Axioms.listened t j₂ = L₂ := by
    simp [MusicStreaming.Axioms.listened, htj₂, L₂]
  have hL₂ne : L₂.Nonempty := by
    obtain ⟨i0, hi0⟩ : ∃ i0, y i0 ≠ 0 := by
      by_contra h; push_neg at h; exact hy (funext h)
    exact ⟨i0, by simp [L₂]; omega⟩
  have hnotsub : ¬ L₂ ⊆ L₁ := by
    intro hsub
    obtain ⟨k, hk⟩ := hL₂ne
    exact Finset.disjoint_left.mp hdisj (hsub hk) hk
  have hgame : MusicStreaming.Core.game t L₁ = 1 := by
    unfold MusicStreaming.Core.game
    rw [hsupp, Finset.filter_insert, Finset.filter_singleton, hlis₁, hlis₂]
    simp [hnotsub, hj]
  have hcore := (hC t hP).2 L₁ (Finset.subset_univ _)
  rw [hgame] at hcore
  have hcard : (t.support.card : ℝ) = 2 := by
    rw [hsupp, Finset.card_pair hj]; norm_num
  have hrew : ∀ k, MusicStreaming.Axioms.reward I t k = I t k / (∑ i', I t i') * 2 := by
    intro k; simp only [MusicStreaming.Axioms.reward, hcard]
  simp only [hrew] at hcore
  rw [← Finset.sum_mul, ← Finset.sum_div] at hcore
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul] at hcore
  -- sums
  have hsumt : ∑ i, I t i = ∑ i, I t₁ i + ∑ i, I t₂ i := by
    rw [hadd]; simp [Finset.sum_add_distrib]
  have hL₁sum₁ : ∑ i ∈ L₁, I t₁ i = ∑ i, I t₁ i := by
    refine Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => ?_)
    apply one_user_vanish n I hI hC j₁ x hx hPx k
    simpa [L₁] using hk
  have hL₁sum₂ : ∑ i ∈ L₁, I t₂ i = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    apply one_user_vanish n I hI hC j₂ y hy hPy k
    by_contra hne
    exact Finset.disjoint_left.mp hdisj hk (by simp [L₂]; omega)
  have hL₁t : ∑ i ∈ L₁, I t i = ∑ i, I t₁ i := by
    rw [hadd]; simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, hL₁sum₁, hL₁sum₂, add_zero]
  rw [hL₁t, hsumt] at hcore
  linarith

end MS3C

theorem solution (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hA : AdditivityOn I) (hC : CoreSelectionOn I) (j₁ j₂ : ℕ) (x y : Fin n → ℕ)
    (hj : j₁ ≠ j₂) (hx : x ≠ 0) (hy : y ≠ 0)
    (hPx : InPStar (Finsupp.single j₁ x)) (hPy : InPStar (Finsupp.single j₂ y))
    (hdisj : Disjoint (Finset.univ.filter (fun i => 0 < x i))
      (Finset.univ.filter (fun i => 0 < y i))) :
    ∑ i, I (Finsupp.single j₁ x) i = ∑ i, I (Finsupp.single j₂ y) i :=
  le_antisymm (MS3C.claim_half n I hI hA hC j₂ j₁ y x (Ne.symm hj) hy hx hPy hPx hdisj.symm)
    (MS3C.claim_half n I hI hA hC j₁ j₂ x y hj hx hy hPx hPy hdisj)
