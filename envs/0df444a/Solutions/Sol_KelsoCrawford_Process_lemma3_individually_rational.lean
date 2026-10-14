-- Prove2me | solution 1 for KelsoCrawford.Process.lemma3_individually_rational
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:03:14.927157+00:00
-- url     : https://prove2.me/submissions/82f35442-92db-47ea-9545-0f42e01e0238

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process



namespace KelsoCrawford.Process

theorem kc_has_offer {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (ρ : Run W F) (h : M.IsRun δ ρ) :
    ∀ t (i : W), ∃ j, i ∈ ρ.offers t j := by
  obtain ⟨⟨_, h0⟩, h2, h3, _⟩ := h
  intro t
  induction t with
  | zero => intro i; exact ⟨Classical.arbitrary F, by rw [h0]; simp⟩
  | succ t ih =>
    intro i
    have hc := (h3 t i (ih i)).1
    refine ⟨ρ.choice t i, (h2 t (ρ.choice t i)).2 ?_⟩
    simp only [Finset.mem_filter]
    exact ⟨hc, fun hr => hr.2 rfl⟩

theorem kc_sal_ge {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (ρ : Run W F) (h : M.IsRun δ ρ) :
    ∀ t i j, M.σ i j ≤ ρ.sal t i j := by
  obtain ⟨⟨hs0, _⟩, _, _, h4⟩ := h
  intro t
  induction t with
  | zero => intro i j; rw [hs0]
  | succ t ih =>
    intro i j
    rw [h4]
    split_ifs
    · linarith [ih i j]
    · exact ih i j

theorem kc_mp_univ {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
    (M : Market W F) (hMP : M.MP) (hNFL : M.NFL) (j : F) :
    ∀ C : Finset W, 0 ≤ profit (M.y j) C (fun i => M.σ i j) := by
  intro C
  induction C using Finset.induction_on with
  | empty => simp [profit, hNFL j]
  | insert a C ha ih =>
    have := hMP a j C ha
    simp only [profit, Finset.sum_insert ha] at ih ⊢
    linarith

theorem kc_ir_core {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hMP : M.MP) (hNFL : M.NFL) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T : ℕ, ρ.Stopped T → M.IsIR (ρ.outcome T) := by
  intro ρ h T hT
  have hoff := kc_has_offer M δ ρ h
  have hsal := kc_sal_ge M δ hδ ρ h
  obtain ⟨⟨hs0, h0⟩, h2, h3, h4⟩ := h
  refine ⟨fun i => hsal T i _, fun j => ?_⟩
  have hh : (ρ.outcome T).hired j = ρ.offers T j := by
    ext i
    show i ∈ Finset.univ.filter (fun i => ρ.choice T i = j) ↔ _
    rw [Finset.mem_filter]; simp only [Finset.mem_univ, true_and]
    constructor
    · rintro rfl; exact (h3 T i (hoff T i)).1
    · intro hi; by_contra hne; exact hT i j ⟨hi, hne⟩
  have hp : profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal
      = profit (M.y j) (ρ.offers T j) (fun i => ρ.sal T i j) := by
    rw [hh]; unfold profit; congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Run.outcome]
    have : ρ.choice T i = j := by by_contra hne; exact hT i j ⟨hi, hne⟩
    rw [this]
  rw [hp]
  cases T with
  | zero =>
    rw [h0]
    have := kc_mp_univ M hMP hNFL j Finset.univ
    simpa [hs0] using this
  | succ t =>
    have := (h2 t j).1 ∅
    simp only [profit, Finset.sum_empty, hNFL j, sub_zero] at this
    simpa [profit] using this

end KelsoCrawford.Process

open KelsoCrawford.Process


theorem solution
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T : ℕ, ρ.Stopped T → M.IsIR (ρ.outcome T) := by
  exact kc_ir_core M δ hδ hMP hNFL
