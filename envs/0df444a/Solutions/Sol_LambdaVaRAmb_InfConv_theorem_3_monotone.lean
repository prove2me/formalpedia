-- Prove2me | solution 1 for LambdaVaRAmb.InfConv.theorem_3_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:11:24.20574+00:00
-- url     : https://prove2.me/submissions/22fee866-858c-4d5c-9d6a-b5eb76e376cc

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting
set_option autoImplicit false
open LambdaVaRAmb.InfConv

theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (𝒜 : Fin n → ℝ → Set (Set Ω)) (h𝒜 : ∀ i x, IsDownset (𝒜 i x)) :
    ((∀ i, Monotone (𝒜 i)) → Monotone (convFamily 𝒜)) ∧
      ((∀ i, Antitone (𝒜 i)) → Antitone (convFamily 𝒜)) := by
  classical
  obtain ⟨i0, -⟩ : ∃ i0 : Fin n, True := ⟨⟨0, hn⟩, trivial⟩
  have hsum : ∀ (y0 : Fin n → ℝ) (d : ℝ),
      ∑ i, Function.update y0 i0 (y0 i0 + d) i = ∑ i, y0 i + d := by
    intro y0 d
    rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    have : ∑ i ∈ Finset.univ \ {i0}, y0 i = ∑ i, y0 i - y0 i0 := by
      rw [Finset.sum_sdiff_eq_sub (by simp)]; simp
    rw [this]; ring
  constructor
  · intro hmono x z hxz E ⟨y0, hy0, A, hA, hE⟩
    refine ⟨Function.update y0 i0 (y0 i0 + (z - x)), ?_, A, ?_, hE⟩
    · rw [hsum, hy0]; ring
    · intro i
      by_cases h : i = i0
      · rw [h]
        simp only [Function.update_self]
        exact hmono i0 (by linarith) (hA i0)
      · simp only [Function.update_of_ne h]; exact hA i
  · intro hanti x z hxz E ⟨y0, hy0, A, hA, hE⟩
    refine ⟨Function.update y0 i0 (y0 i0 + (x - z)), ?_, A, ?_, hE⟩
    · rw [hsum, hy0]; ring
    · intro i
      by_cases h : i = i0
      · rw [h]
        simp only [Function.update_self]
        exact hanti i0 (by linarith) (hA i0)
      · simp only [Function.update_of_ne h]; exact hA i
