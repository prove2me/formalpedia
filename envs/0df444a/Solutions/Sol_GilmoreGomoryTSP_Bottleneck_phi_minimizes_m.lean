-- Prove2me | solution 1 for GilmoreGomoryTSP.Bottleneck.phi_minimizes_m
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:13:10.144972+00:00
-- url     : https://prove2.me/submissions/d7d8c19e-6731-420d-9d71-b97cfc6eef8d

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model



namespace GilmoreGomoryTSP.Bottleneck

open MeasureTheory

lemma gg_c_nonneg {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (i j : Fin (n + 1)) :
    0 ≤ GilmoreGomoryTSP.MinCost.c f g A B i j := by
  unfold GilmoreGomoryTSP.MinCost.c
  split_ifs with h
  · exact intervalIntegral.integral_nonneg h (fun x _ => hf0 x)
  · simp [hg0]

lemma gg_c_anti {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    {i i' j j' : Fin (n + 1)} (hB : B i ≤ B i') (hA : A j' ≤ A j) :
    GilmoreGomoryTSP.MinCost.c f g A B i' j' ≤ GilmoreGomoryTSP.MinCost.c f g A B i j := by
  by_cases h' : B i' ≤ A j'
  · have h : B i ≤ A j := by linarith
    have e1 : GilmoreGomoryTSP.MinCost.c f g A B i' j' = ∫ x in B i'..A j', f x := by
      simp [GilmoreGomoryTSP.MinCost.c, h']
    have e2 : GilmoreGomoryTSP.MinCost.c f g A B i j = ∫ x in B i..A j, f x := by
      simp [GilmoreGomoryTSP.MinCost.c, h]
    rw [e1, e2]
    exact intervalIntegral.integral_mono_interval hB h' hA
      (Filter.Eventually.of_forall (fun x => hf0 x)) (MeasureTheory.IntegrableOn.intervalIntegrable (hf.integrableOn_isCompact isCompact_uIcc))
  · have e1 : GilmoreGomoryTSP.MinCost.c f g A B i' j' = 0 := by
      simp [GilmoreGomoryTSP.MinCost.c, h', hg0]
    rw [e1]
    exact gg_c_nonneg f g A B hf0 hg0 i j

lemma gg_exists_a {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (q : Fin n)
    (h : ∃ j : Fin (n + 1), (σ j : ℕ) ≤ q ∧ (q : ℕ) < j) : ∃ i : Fin (n + 1), (i : ℕ) ≤ q ∧ (q : ℕ) < σ i := by
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj1, hj2⟩ := h
  have hsub : (Finset.Iic q.castSucc).image σ ⊆ Finset.Iic q.castSucc := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Iic] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Fin.le_def] at hy ⊢
    exact hne y (by simpa using hy)
  have hcard : ((Finset.Iic q.castSucc).image σ).card = (Finset.Iic q.castSucc).card :=
    Finset.card_image_of_injective _ σ.injective
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hmem : σ j ∈ Finset.Iic q.castSucc := by
    simp only [Finset.mem_Iic, Fin.le_def]; simpa using hj1
  rw [← heq] at hmem
  simp only [Finset.mem_image, Finset.mem_Iic] at hmem
  obtain ⟨x, hx, hxj⟩ := hmem
  have := σ.injective hxj
  subst this
  rw [Fin.le_def] at hx
  simp at hx
  omega

theorem gg_eq30 {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ))
    (ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) (hq : q ∈ starArcs φ ψ) :
    arcCost f g A B φ q ≤ m f g A B ψ := by
  unfold starArcs at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  have hex : ∃ i : Fin (n + 1), (i : ℕ) ≤ q ∧ (q : ℕ) < (φ.symm (ψ i) : ℕ) := by
    rcases hq with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨i, hi⟩
    · exact gg_exists_a (ψ.trans φ.symm) q ⟨j, hj⟩
  obtain ⟨i, hi1, hi2⟩ := hex
  have hBi : B i ≤ B q.castSucc := hB (by rw [Fin.le_def]; simpa using hi1)
  have hAi : A (φ q.succ) ≤ A (ψ i) := by
    have := hφ (show q.succ ≤ φ.symm (ψ i) by rw [Fin.le_def]; simpa using hi2)
    simpa using this
  have := gg_c_anti f g A B hf0 hg0 hf hBi hAi
  refine le_trans this ?_
  exact Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i)) (Finset.mem_univ i)

theorem gg_phi_min {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), m f g A B φ ≤ m f g A B ψ := by
  intro ψ
  unfold m
  apply Finset.sup'_le
  intro i _
  have hex : ∃ j, j ≤ i ∧ i ≤ φ.symm (ψ j) := by
    by_contra hne
    push_neg at hne
    have hsub : (Finset.Iic i).image (ψ.trans φ.symm) ⊆ Finset.Iio i := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_Iic, Finset.mem_Iio] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact hne y hy
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (ψ.trans φ.symm).injective] at h1
    simp [Fin.card_Iic, Fin.card_Iio] at h1
  obtain ⟨j, hj1, hj2⟩ := hex
  have hBj : B j ≤ B i := hB hj1
  have hAj : A (φ i) ≤ A (ψ j) := by
    have := hφ hj2
    simpa using this
  have := gg_c_anti f g A B hf0 hg0 hf hBj hAj
  refine le_trans this ?_
  exact Finset.le_sup' (fun i => GilmoreGomoryTSP.MinCost.c f g A B i (ψ i)) (Finset.mem_univ j)

end GilmoreGomoryTSP.Bottleneck

open GilmoreGomoryTSP.Bottleneck


theorem solution {n : ℕ} (f g : ℝ → ℝ) (A B : Fin (n + 1) → ℝ) (hB : Monotone B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, g x = 0) (hf : MeasureTheory.LocallyIntegrable f)
    (φ : Equiv.Perm (Fin (n + 1))) (hφ : Monotone (A ∘ φ)) :
    ∀ ψ : Equiv.Perm (Fin (n + 1)), m f g A B φ ≤ m f g A B ψ := by
  exact gg_phi_min f g A B hB hf0 hg0 hf φ hφ
