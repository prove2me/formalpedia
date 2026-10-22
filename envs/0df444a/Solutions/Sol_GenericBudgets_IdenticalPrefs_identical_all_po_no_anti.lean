-- Prove2me | solution 1 for GenericBudgets.IdenticalPrefs.identical_all_po_no_anti
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:44:27.101554+00:00
-- url     : https://prove2.me/submissions/6319baed-63c1-4efc-adc5-fc4c2e47503f

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting
set_option autoImplicit false
open GenericBudgets.AlmostEqual

theorem solution {m : ℕ} (v : Fin 2 → Finset (Fin m) → ℝ)
    (hv : ∀ i, GenericBudgets.AlmostEqual.IsStandardValuation (v i)) (hsame : v 0 = v 1)
    (b : Fin 2 → ℝ) (hb : ∀ i, 0 < b i) (hsum : b 0 + b 1 = 1) :
    (∀ σ, GenericBudgets.AlmostEqual.IsPO v σ) ∧ ∀ σ, ¬ GenericBudgets.AlmostEqual.IsAntiProportional v b σ := by
  have hw := hv 0
  have hsplit : ∀ σ : Fin m → Fin 2, v 0 (bundle σ 0) + v 0 (bundle σ 1) = 1 := by
    intro σ
    rw [hw.additive (bundle σ 0), hw.additive (bundle σ 1), ← hw.normalized, hw.additive Finset.univ]
    unfold bundle
    have : (Finset.univ.filter fun j : Fin m => σ j = 1) = Finset.univ.filter fun j : Fin m => ¬ σ j = 0 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : ∀ a : Fin 2, a = 1 ↔ ¬ a = 0 := by decide
      exact this _
    rw [this, Finset.sum_filter_add_sum_filter_not]
  have h1 : ∀ σ : Fin m → Fin 2, v 1 (bundle σ 1) = v 0 (bundle σ 1) := fun σ => by rw [hsame]
  have h0 : ∀ σ : Fin m → Fin 2, v 1 (bundle σ 0) = v 0 (bundle σ 0) := fun σ => by rw [hsame]
  constructor
  · intro σ σ' hne
    have hB : bundle σ' 0 ≠ bundle σ 0 := by
      intro h
      apply hne
      funext j
      have := Finset.ext_iff.mp h j
      simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and] at this
      have key : ∀ a c : Fin 2, (a = 0 ↔ c = 0) → a = c := by decide
      exact key _ _ this
    have hne' : v 0 (bundle σ' 0) ≠ v 0 (bundle σ 0) := fun h => hB (hw.strict h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact ⟨0, h⟩
    · refine ⟨1, ?_⟩
      have := hsplit σ; have := hsplit σ'
      rw [h1, h1]
      linarith
  · intro σ ⟨hle, i, hi⟩
    have hn : v 0 Finset.univ = 1 := hw.normalized
    have e0 := hle 0
    have e1 := hle 1
    rw [h1 σ] at e1
    have hn1 : v 1 Finset.univ = 1 := by rw [← hsame]; exact hn
    rw [hn] at e0
    rw [hn1] at e1
    have := hsplit σ
    fin_cases i
    · simp only [Fin.zero_eta, hn] at hi
      linarith
    · simp only [Fin.mk_one, hn1] at hi
      rw [h1] at hi
      linarith
