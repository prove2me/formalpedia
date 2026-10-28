-- Prove2me | solution 1 for LambdaVaRAmb.Robust.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:27:26.330065+00:00
-- url     : https://prove2.me/submissions/b9e3661c-a552-4611-8ac8-99d3e92f2580

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting
import Theorems.Thm_LambdaVaRAmb_Robust_proposition_2

open MeasureTheory LambdaVaRAmb.Robust

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (Pcl : Set (Measure Ω)) (hPcl : Pcl.Nonempty) (hprob : ∀ Q ∈ Pcl, IsProbabilityMeasure Q)
    (Λ : ℝ → ℝ) (hΛ : InHI Λ) :
    IsCapacity (upperProb Pcl) ∧ IsCapacity (lowerProb Pcl) ∧
      ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ Pcl, LVaR Λ (probCap Q) X) = LVaR Λ (upperProb Pcl) X ∧
          (⨅ Q ∈ Pcl, LVaRPlus Λ (probCap Q) X) = LVaRPlus Λ (lowerProb Pcl) X := by
  set W := probCap '' Pcl with hWdef
  have hW : W.Nonempty := hPcl.image _
  have hcap : ∀ w ∈ W, IsCapacity w := by
    rintro _ ⟨Q, hQ, rfl⟩
    haveI := hprob Q hQ
    exact { nonneg := fun A _ => measureReal_nonneg
            le_one := fun A _ => measureReal_le_one
            mono := fun A B _ _ hAB => measureReal_mono hAB
            empty := by simp [probCap]
            univ := by simp [probCap] }
  have hne : ∀ A : Set Ω, ((fun w : Set Ω → ℝ => w A) '' W).Nonempty := fun A => hW.image _
  have hbdd : ∀ A, MeasurableSet A → BddAbove ((fun w : Set Ω → ℝ => w A) '' W) := by
    intro A hA; refine ⟨1, ?_⟩; rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).le_one _ hA
  have hbddb : ∀ A, MeasurableSet A → BddBelow ((fun w : Set Ω → ℝ => w A) '' W) := by
    intro A hA; refine ⟨0, ?_⟩; rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).nonneg _ hA
  have hconst : ∀ (A : Set Ω) (c : ℝ), (∀ w ∈ W, w A = c) →
      (fun w : Set Ω → ℝ => w A) '' W = {c} := by
    intro A c hc
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩; exact hc w hw
    · rintro rfl; obtain ⟨w, hw⟩ := hW; exact ⟨w, hw, hc w hw⟩
  refine ⟨?_, ?_, ?_⟩
  · exact
    { nonneg := fun A hA => by
        obtain ⟨w, hw⟩ := hW
        exact le_trans ((hcap w hw).nonneg A hA) (le_csSup (hbdd A hA) ⟨w, hw, rfl⟩)
      le_one := fun A hA => csSup_le (hne A) (by
        rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).le_one A hA)
      mono := fun A B hA hB hAB => csSup_le (hne A) (by
        rintro _ ⟨w, hw, rfl⟩
        exact le_trans ((hcap w hw).mono A B hA hB hAB) (le_csSup (hbdd B hB) ⟨w, hw, rfl⟩))
      empty := by
        show sSup _ = _
        rw [hconst ∅ 0 (fun w hw => (hcap w hw).empty), csSup_singleton]
      univ := by
        show sSup _ = _
        rw [hconst Set.univ 1 (fun w hw => (hcap w hw).univ), csSup_singleton] }
  · exact
    { nonneg := fun A hA => le_csInf (hne A) (by
        rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).nonneg A hA)
      le_one := fun A hA => by
        obtain ⟨w, hw⟩ := hW
        exact le_trans (csInf_le (hbddb A hA) ⟨w, hw, rfl⟩) ((hcap w hw).le_one A hA)
      mono := fun A B hA hB hAB => le_csInf (hne B) (by
        rintro _ ⟨w, hw, rfl⟩
        exact le_trans (csInf_le (hbddb A hA) ⟨w, hw, rfl⟩) ((hcap w hw).mono A B hA hB hAB))
      empty := by
        show sInf _ = _
        rw [hconst ∅ 0 (fun w hw => (hcap w hw).empty), csInf_singleton]
      univ := by
        show sInf _ = _
        rw [hconst Set.univ 1 (fun w hw => (hcap w hw).univ), csInf_singleton] }
  · intro X hX
    obtain ⟨h1, h2⟩ := LambdaVaRAmb.Robust.proposition_2 W hW hcap Λ hΛ X hX
    refine ⟨?_, ?_⟩
    · rw [upperProb, ← h1, hWdef, iSup_image]
    · rw [lowerProb, ← h2, hWdef, iInf_image]
