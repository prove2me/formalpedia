-- Prove2me | solution 1 for GrayStability.gray_stability
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:54:30.930219+00:00
-- url     : https://prove2.me/submissions/a6ee5eae-50c8-4dbf-8d68-feafca9627aa

import Theorems.Thm_GrayStability_gray_stability_conformal

set_option autoImplicit false
open GrayStability

theorem solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        (α 0 y v = 0 ↔ pullback (ψ t) (α t) y v = 0) := by
  obtain ⟨ψ, hψ, lam, _, hpos, hconf⟩ := gray_stability_conformal F hF α hα
  refine ⟨ψ, hψ, ?_⟩
  intro t ht y hy v hv
  rw [hconf t ht y hy v hv]
  exact (mul_eq_zero_iff_left (ne_of_gt (hpos t ht y hy))).symm
