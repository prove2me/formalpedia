-- Prove2me | solution 1 for InvShareComp.Exog.lemma_3c_t
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:00:11.587336+00:00
-- url     : https://prove2.me/submissions/a36944fb-f020-4288-95e6-798682d87889

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model
import Theorems.Thm_InvShareComp_Exog_proposition_1a
import Theorems.Thm_InvShareComp_Exog_closed_form_profits

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (hS0 : 0 ≤ SVal P ν (P.cbar - P.δ) I) :
    MonotoneOn (fun t => piHat P ν t I) (Set.Icc 0 (P.cbar - P.δ)) := by
  have hP' := hP
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  have hk2 : 0 < 2 * P.k := by linarith
  have htop : P.cbar - P.δ ∈ Set.Icc 0 (P.cbar - P.δ) := ⟨by linarith, le_refl _⟩
  -- ŝ(a) - ŝ(b) = 2 (b - a) β W / (2k)
  have hdiff : ∀ a ∈ Set.Icc 0 (P.cbar - P.δ), ∀ b ∈ Set.Icc 0 (P.cbar - P.δ), a ≤ b →
      sHat P ν b I ≤ sHat P ν a I := by
    intro a ha b hb hab
    obtain ⟨ia, hW0, -⟩ := proposition_1a P hP' ν hν I hI a ha
    obtain ⟨ib, -, -⟩ := proposition_1a P hP' ν hν I hI b hb
    have e : sHat P ν a I - sHat P ν b I = 2 * (b - a) * P.β * Wval ν I / (2 * P.k) := by
      have : sHat P ν a I - sHat P ν b I
          = (sHat P ν a I - sHatN P ν I) - (sHat P ν b I - sHatN P ν I) := by ring
      rw [this, ia, ib]; field_simp; ring
    have : 0 ≤ 2 * (b - a) * P.β * Wval ν I / (2 * P.k) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hβ) hW0) hk2.le
    linarith
  have hsTop : 0 ≤ sHat P ν (P.cbar - P.δ) I := by
    unfold sHat; exact div_nonneg (mul_nonneg hβ hS0) hk2.le
  intro a ha b hb hab
  have hba := hdiff a ha b hb hab
  have hb0 : 0 ≤ sHat P ν b I := le_trans hsTop (hdiff b hb _ htop hb.2)
  have hsq : sHat P ν b I ^ 2 ≤ sHat P ν a I ^ 2 := pow_le_pow_left₀ hb0 hba 2
  obtain ⟨-, ca⟩ := closed_form_profits P hP' ν hν I hI a ha
  obtain ⟨-, cb⟩ := closed_form_profits P hP' ν hν I hI b hb
  show piHat P ν a I ≤ piHat P ν b I
  unfold piHat
  rw [ca, cb]
  nlinarith
