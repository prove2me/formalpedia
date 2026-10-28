-- Prove2me | solution 1 for LambdaVaRAmb.Robust.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:26:24.45196+00:00
-- url     : https://prove2.me/submissions/f2d2dcdb-8c08-4d8a-a893-1abbc434c138

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

open MeasureTheory LambdaVaRAmb.Robust

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (W : Set (Set Ω → ℝ)) (hW : W.Nonempty) (hcap : ∀ w ∈ W, IsCapacity w)
    (Λ : ℝ → ℝ) (hΛ : InHI Λ) (X : Ω → ℝ) (hX : Measurable X) :
    (⨆ w ∈ W, LVaR Λ w X) = LVaR Λ (upperCap W) X ∧
      (⨅ w ∈ W, LVaRPlus Λ w X) = LVaRPlus Λ (lowerCap W) X := by
  have hm : ∀ x : ℝ, MeasurableSet {ω | x < X ω} := fun x => measurableSet_lt measurable_const hX
  have hne : ∀ A : Set Ω, ((fun w : Set Ω → ℝ => w A) '' W).Nonempty := fun A => hW.image _
  have hbdd : ∀ x : ℝ, BddAbove ((fun w : Set Ω → ℝ => w {ω | x < X ω}) '' W) := by
    intro x; refine ⟨1, ?_⟩; rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).le_one _ (hm x)
  have hbddb : ∀ x : ℝ, BddBelow ((fun w : Set Ω → ℝ => w {ω | x < X ω}) '' W) := by
    intro x; refine ⟨0, ?_⟩; rintro _ ⟨w, hw, rfl⟩; exact (hcap w hw).nonneg _ (hm x)
  have hup : ∀ w ∈ W, ∀ x : ℝ, w {ω | x < X ω} ≤ upperCap W {ω | x < X ω} :=
    fun w hw x => le_csSup (hbdd x) ⟨w, hw, rfl⟩
  have hlow : ∀ w ∈ W, ∀ x : ℝ, lowerCap W {ω | x < X ω} ≤ w {ω | x < X ω} :=
    fun w hw x => csInf_le (hbddb x) ⟨w, hw, rfl⟩
  have hmono : ∀ w ∈ W, ∀ z x : ℝ, z ≤ x → w {ω | x < X ω} ≤ w {ω | z < X ω} := by
    intro w hw z x hzx
    exact (hcap w hw).mono _ _ (hm x) (hm z) (fun ω hω => lt_of_le_of_lt hzx hω)
  constructor
  · apply le_antisymm
    · refine iSup₂_le fun w hw => ?_
      apply sInf_le_sInf
      apply Set.image_mono
      intro x hx
      exact le_trans (hup w hw x) hx
    · by_contra hcon
      push_neg at hcon
      obtain ⟨x', h1, h2⟩ := EReal.exists_between_coe_real hcon
      have hx' : x' ∉ {x : ℝ | upperCap W {ω | x < X ω} ≤ Λ x} := by
        intro hx
        have : LVaR Λ (upperCap W) X ≤ (x' : EReal) := sInf_le ⟨x', hx, rfl⟩
        exact absurd this (not_le.2 h2)
      simp only [Set.mem_setOf_eq, not_le] at hx'
      obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne _) hx'
      have : (x' : EReal) ≤ LVaR Λ w X := by
        apply le_sInf
        rintro _ ⟨z, hz, rfl⟩
        simp only [Set.mem_setOf_eq] at hz
        by_contra hzx
        push_neg at hzx
        have hzx' : z ≤ x' := EReal.coe_le_coe_iff.1 hzx.le
        have := hmono w hw z x' hzx'
        have := hΛ.2 hzx'
        linarith
      have : LVaR Λ w X ≤ ⨆ w ∈ W, LVaR Λ w X := le_iSup₂ (f := fun w _ => LVaR Λ w X) w hw
      exact absurd (lt_of_lt_of_le h1 (by order)) (lt_irrefl _)
  · apply le_antisymm
    · by_contra hcon
      push_neg at hcon
      obtain ⟨x', h1, h2⟩ := EReal.exists_between_coe_real hcon
      have hx' : x' ∉ {x : ℝ | Λ x ≤ lowerCap W {ω | x < X ω}} := by
        intro hx
        have : (x' : EReal) ≤ LVaRPlus Λ (lowerCap W) X := le_sSup ⟨x', hx, rfl⟩
        exact absurd this (not_le.2 h1)
      simp only [Set.mem_setOf_eq, not_le] at hx'
      obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne _) hx'
      have : LVaRPlus Λ w X ≤ (x' : EReal) := by
        apply sSup_le
        rintro _ ⟨z, hz, rfl⟩
        simp only [Set.mem_setOf_eq] at hz
        by_contra hzx
        push_neg at hzx
        have hzx' : x' ≤ z := EReal.coe_le_coe_iff.1 hzx.le
        have := hmono w hw x' z hzx'
        have := hΛ.2 hzx'
        linarith
      have : ⨅ w ∈ W, LVaRPlus Λ w X ≤ LVaRPlus Λ w X :=
        iInf₂_le (f := fun w _ => LVaRPlus Λ w X) w hw
      exact absurd (lt_of_le_of_lt (by order) h2) (lt_irrefl _)
    · refine le_iInf₂ fun w hw => ?_
      apply sSup_le_sSup
      apply Set.image_mono
      intro x hx
      exact le_trans hx (hlow w hw x)
