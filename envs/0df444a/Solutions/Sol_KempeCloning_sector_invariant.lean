-- Prove2me | solution 1 for KempeCloning.sector_invariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:12:34.471613+00:00
-- url     : https://prove2.me/submissions/a0a17364-43b1-4b53-86c6-e849a3869df0

import Mathlib
import Definitions.Def_KempeCloning_ham
import Definitions.Def_KempeCloning_sectorIndex

namespace Aux_KCsec

open KempeCloning

theorem cre_single (k : Mode) (n : FockIndex) :
    cre k (Finsupp.single n 1) =
      ((Real.sqrt ((n k : ℝ) + 1) : ℝ) : ℂ) • Finsupp.single (Function.update n k (n k + 1)) 1 := by
  unfold cre; rw [Finsupp.linearCombination_single, one_smul]

theorem ann_single_zero (k : Mode) (n : FockIndex) (h : n k = 0) :
    ann k (Finsupp.single n 1) = 0 := by
  unfold ann; rw [Finsupp.linearCombination_single, if_pos h, smul_zero]

theorem ann_single_ne (k : Mode) (n : FockIndex) (h : n k ≠ 0) :
    ann k (Finsupp.single n 1) =
      ((Real.sqrt (n k : ℝ) : ℝ) : ℂ) • Finsupp.single (Function.update n k (n k - 1)) 1 := by
  unfold ann; rw [Finsupp.linearCombination_single, if_neg h, one_smul]

theorem mem_of_ann (k : Mode) (n : FockIndex) (S : Set FockIndex)
    (h : n k ≠ 0 → Function.update n k (n k - 1) ∈ S) :
    ann k (Finsupp.single n 1) ∈ Finsupp.supported ℂ ℂ S := by
  by_cases hk : n k = 0
  · rw [ann_single_zero k n hk]; exact Submodule.zero_mem _
  · rw [ann_single_ne k n hk]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ 1 (h hk))

end Aux_KCsec

open KempeCloning Aux_KCsec Mode in
theorem solution (γ : ℝ) (m N : ℕ) (q : Sector N) :
    ∀ n ∈ (ham γ (Finsupp.single (sectorIndex m N q) 1)).support,
      n ∈ Set.range (sectorIndex m N) := by
  obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩ := q
  simp only at hxy
  set S := Set.range (sectorIndex m N) with hS
  set s := sectorIndex m N ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩ with hs
  have hsv : ∀ k, s k = occ (m + y) x x y (N - x - y) k := fun k => rfl
  -- term 1: ann a1 ∘ ann b2 ∘ cre c
  have T1 : (ann a1 ∘ₗ ann b2 ∘ₗ cre c) (Finsupp.single s 1) ∈ Finsupp.supported ℂ ℂ S := by
    show ann a1 (ann b2 (cre c (Finsupp.single s 1))) ∈ _
    rw [cre_single, map_smul, map_smul]
    apply Submodule.smul_mem
    by_cases hb : (Function.update s c (s c + 1)) b2 = 0
    · rw [ann_single_zero _ _ hb, map_zero]; exact Submodule.zero_mem _
    · rw [ann_single_ne _ _ hb, map_smul]
      apply Submodule.smul_mem
      apply mem_of_ann
      intro _
      simp [Function.update_apply, hsv, occ] at hb
      refine ⟨⟨(⟨x, hx⟩, ⟨y - 1, by omega⟩), by simp only; omega⟩, ?_⟩
      funext k
      cases k <;> simp [Function.update_apply, hsv, sectorIndex, occ] <;> omega
  -- term 2: ann a2 ∘ ann b1 ∘ cre c
  have T2 : (ann a2 ∘ₗ ann b1 ∘ₗ cre c) (Finsupp.single s 1) ∈ Finsupp.supported ℂ ℂ S := by
    show ann a2 (ann b1 (cre c (Finsupp.single s 1))) ∈ _
    rw [cre_single, map_smul, map_smul]
    apply Submodule.smul_mem
    by_cases hb : (Function.update s c (s c + 1)) b1 = 0
    · rw [ann_single_zero _ _ hb, map_zero]; exact Submodule.zero_mem _
    · rw [ann_single_ne _ _ hb, map_smul]
      apply Submodule.smul_mem
      apply mem_of_ann
      intro _
      simp [Function.update_apply, hsv, occ] at hb
      refine ⟨⟨(⟨x - 1, by omega⟩, ⟨y, hy⟩), by simp only; omega⟩, ?_⟩
      funext k
      cases k <;> simp [Function.update_apply, hsv, sectorIndex, occ] <;> omega
  -- term 3: ann c ∘ cre b2 ∘ cre a1
  have T3 : (ann c ∘ₗ cre b2 ∘ₗ cre a1) (Finsupp.single s 1) ∈ Finsupp.supported ℂ ℂ S := by
    show ann c (cre b2 (cre a1 (Finsupp.single s 1))) ∈ _
    rw [cre_single]
    simp only [map_smul]
    rw [cre_single]
    simp only [map_smul]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    apply mem_of_ann
    intro hc
    simp [Function.update_apply, hsv, occ] at hc
    refine ⟨⟨(⟨x, hx⟩, ⟨y + 1, by omega⟩), by simp only; omega⟩, ?_⟩
    funext k
    cases k <;> simp [Function.update_apply, hsv, sectorIndex, occ] <;> omega
  -- term 4: ann c ∘ cre b1 ∘ cre a2
  have T4 : (ann c ∘ₗ cre b1 ∘ₗ cre a2) (Finsupp.single s 1) ∈ Finsupp.supported ℂ ℂ S := by
    show ann c (cre b1 (cre a2 (Finsupp.single s 1))) ∈ _
    rw [cre_single]
    simp only [map_smul]
    rw [cre_single]
    simp only [map_smul]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    apply mem_of_ann
    intro hc
    simp [Function.update_apply, hsv, occ] at hc
    refine ⟨⟨(⟨x + 1, by omega⟩, ⟨y, hy⟩), by simp only; omega⟩, ?_⟩
    funext k
    cases k <;> simp [Function.update_apply, hsv, sectorIndex, occ] <;> omega
  have hmem : ham γ (Finsupp.single s 1) ∈ Finsupp.supported ℂ ℂ S := by
    unfold ham
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ T1 T2))
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ T3 T4))
  intro n hn
  exact (Finsupp.mem_supported ℂ _).mp hmem hn
