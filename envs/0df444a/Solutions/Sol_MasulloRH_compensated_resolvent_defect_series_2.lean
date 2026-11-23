-- Prove2me | solution 2 for MasulloRH.compensated_resolvent_defect_series
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:49.63117+00:00
-- url     : https://prove2.me/submissions/04f7ffc7-b8d7-4c26-ae6d-cd70d185afa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_regularized_initial_identity_iff_scalar_bound
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open MasulloRH

theorem solution
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    ∃ f : ZetaZerosInTraceStrip (1 / 2) → ℝ,
      (∀ ρ, 0 ≤ f ρ) ∧ Summable f ∧
        (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re = ∑' ρ, f ρ :=
  by
  -- Under the Riemann hypothesis every zero of the open critical strip lies in the window of half-width α.
  have hwin : ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |ρ.val.re - 1 / 2| < α := fun ρ => by
    rw [riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
      ρ.val ρ.2.1 ρ.2.2.1 ρ.2.2.2.1, sub_self, abs_zero]
    exact hα
  -- The full-strip trace equals the logarithmic derivative at 3.
  have hfull : regularizedTraceRHS (1 / 2) 3 = zetaLogDeriv 3 :=
    MasulloRH.regularized_initial_identity_full_strip 3 (by norm_num)
  -- The scalar bound at 3, hence the identity for the window of half-width α at 3.
  have hle : (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
    rw [← hfull]
    exact (MasulloRH.single_resolvent_test α).mpr hwin
  have hα3 : regularizedTraceRHS α 3 = zetaLogDeriv 3 :=
    (MasulloRH.regularized_initial_identity_iff_scalar_bound α).mpr hle 3 (by norm_num)
  -- The defect vanishes, and the zero family represents it.
  refine ⟨fun _ => 0, fun _ => le_rfl, summable_zero, ?_⟩
  rw [hα3, hfull, sub_self, tsum_zero]
