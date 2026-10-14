-- Prove2me | solution 1 for KelsoCrawford.OneSided.dummy_firms_zero_profit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:00:00.712723+00:00
-- url     : https://prove2.me/submissions/7d6301ef-b2b5-48d7-b9b5-c156d0f377fe

import Mathlib
import Definitions.Def_KelsoCrawford_OneSided_Model
import Definitions.Def_KelsoCrawford_OneSided_Fictitious



namespace KelsoCrawford.OneSided

theorem dz_core {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (μ : W → ℝ → ℝ)
    (hNFL : v ∅ = 0)
    (hμ : ∀ i, StrictMono (μ i) ∧ Continuous (μ i))
    (A : Allocation W (Fin (Fintype.card W + 1)))
    (hcore : (fictitious v μ).IsStrictCore KelsoCrawford.ContinuousCore.anySalary A) :
    ∀ j, profit v (A.hired j) A.sal = 0 := by
  obtain ⟨hIR, _, hni⟩ := hcore
  have hns : ¬ Function.Surjective A.assign := by
    intro hs
    have := Fintype.card_le_of_surjective _ hs
    simp at this
  obtain ⟨j0, hj0⟩ : ∃ j0, ∀ i, A.assign i ≠ j0 := by
    by_contra hc
    apply hns
    intro b
    by_contra hb
    exact hc ⟨b, fun i hi => hb ⟨i, hi⟩⟩
  have hemp : A.hired j0 = ∅ := by
    unfold Allocation.hired
    ext i; simp [hj0 i]
  have hp0 : profit v (A.hired j0) A.sal = 0 := by
    rw [hemp]; simp [profit, hNFL]
  intro j
  have h0 : 0 ≤ profit v (A.hired j) A.sal := hIR.2 j
  by_contra hne
  have hpos : 0 < profit v (A.hired j) A.sal := lt_of_le_of_ne h0 (Ne.symm hne)
  set p := profit v (A.hired j) A.sal with hp
  set C := A.hired j
  set k : ℝ := (C.card : ℝ) + 1
  have hk : 0 < k := by positivity
  set ε := p / k
  have hε : 0 < ε := div_pos hpos hk
  apply hni
  refine ⟨j0, C, fun i => A.sal i + ε, fun _ _ => Set.mem_univ _, ?_, ?_, Or.inr ?_⟩
  · intro i _
    show μ i (A.sal i) ≤ μ i (A.sal i + ε)
    exact (hμ i).1.monotone (by linarith)
  · have : profit v C (fun i => A.sal i + ε) = p - C.card * ε := by
      simp only [hp, profit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    show profit v (A.hired j0) A.sal ≤ profit v C (fun i => A.sal i + ε)
    rw [hp0, this]
    have : (C.card : ℝ) * ε = p - ε := by
      simp only [ε]; field_simp; simp only [k]; ring
    linarith
  · have : profit v C (fun i => A.sal i + ε) = p - C.card * ε := by
      simp only [hp, profit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    show profit v (A.hired j0) A.sal < profit v C (fun i => A.sal i + ε)
    rw [hp0, this]
    have : (C.card : ℝ) * ε = p - ε := by
      simp only [ε]; field_simp; simp only [k]; ring
    linarith

end KelsoCrawford.OneSided

open KelsoCrawford.OneSided


theorem solution {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (μ : W → ℝ → ℝ)
    (hMP : ∀ i (C : Finset W), 0 ≤ v (insert i C) - v C)
    (hNFL : v ∅ = 0)
    (hμ : ∀ i, StrictMono (μ i) ∧ Continuous (μ i))
    (A : Allocation W (Fin (Fintype.card W + 1)))
    (hcore : (fictitious v μ).IsStrictCore KelsoCrawford.ContinuousCore.anySalary A) :
    ∀ j, profit v (A.hired j) A.sal = 0 := by
  exact dz_core v μ hNFL hμ A hcore
