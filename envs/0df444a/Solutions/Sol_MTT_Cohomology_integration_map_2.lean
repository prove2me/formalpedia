-- Prove2me | solution 2 for MTT.Cohomology.integration_map
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T16:51:42.445472+00:00
-- url     : https://prove2.me/submissions/8e1f4a0f-6029-4f81-8185-cd8c14af49d2

import Definitions.Def_MTT_Cohomology
import Theorems.Thm_MTT_Cohomology_integration_map_exists
import Theorems.Thm_MTT_period_vanishing

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ,
      Function.Injective I ∧ HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hT, hI⟩ := MTT.Cohomology.integration_map_exists hN hk
  refine ⟨I, ?_, hT, hI⟩
  intro f g hfg
  have h0 : I (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hper : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
      MTT.modularIntegral (f - g) (Polynomial.X ^ j) r = 0 := by
    intro j hj r
    have hev := hI (f - g) j r hj
    rw [h0] at hev
    simp only [map_zero] at hev
    have hbin : ((k - 2).choose j : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
    exact (mul_eq_zero.mp hev.symm).resolve_left hbin
  exact sub_eq_zero.mp (MTT.period_vanishing hN hk (f - g) hper)
