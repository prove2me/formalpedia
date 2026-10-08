-- Prove2me | solution 1 for MechanismDesign.IncentiveCompat.ir_lowest_type
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:21:16.366883+00:00
-- url     : https://prove2.me/submissions/07c69a7a-a1e3-4631-bdd9-81302aa7fd88

import Definitions.Def_MechanismDesign_IncentiveCompat_Model
set_option autoImplicit false
open MechanismDesign.IncentiveCompat

theorem solution {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ) (R : A → A → Prop)
    (hR : IsCompleteTransitive R) (h1 : OneDimensional u R) (θlo : Θ)
    (hθlo : ∀ θ : Θ, θ ≠ θlo → HigherType u R θ θlo) (alo : A)
    (halo : ∀ b : A, b ≠ alo → R b alo) (M : DirectMechanism A Θ) (hIC : IsIC u M) :
    IsIRWith u M alo ↔ u alo θlo ≤ u (M.q θlo) θlo - M.t θlo := by
  constructor
  · intro h
    exact h θlo
  · intro hlo θ
    by_cases heq : θ = θlo
    · subst θ
      exact hlo
    have hh := hθlo θ heq
    have hr : R (M.q θlo) alo := by
      by_cases ha : M.q θlo = alo
      · rw [ha]
        exact (hR.1 alo alo).elim id id
      · exact halo _ ha
    have hdiff : u (M.q θlo) θlo - u alo θlo ≤ u (M.q θlo) θ - u alo θ := by
      by_cases hrev : R alo (M.q θlo)
      · exact (hh.2 (M.q θlo) alo ⟨hr,hrev⟩).1.ge
      · exact (hh.1 (M.q θlo) alo ⟨hr,hrev⟩).le
    have hic := hIC θ θlo
    linarith
