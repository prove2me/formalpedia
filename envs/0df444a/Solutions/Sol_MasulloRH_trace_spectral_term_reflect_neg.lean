-- Prove2me | solution 1 for MasulloRH.trace_spectral_term_reflect_neg
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T02:03:09.60258+00:00
-- url     : https://prove2.me/submissions/beb5f3c2-30cc-4eb6-ab2b-40a16979a077

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff
open MasulloRH

theorem solution (α : ℝ) (φ : ℝ → ℂ)
    (e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α)
    (hcenter : ∀ ρ, (e ρ).val = 1 - ρ.val)
    (hmult : ∀ ρ, analyticOrderNatAt riemannZeta ((e ρ).val) =
      analyticOrderNatAt riemannZeta (ρ.val))
    (hodd : ∀ t : ℝ, φ t⁻¹ = -φ t) :
    ∀ ρ, zetaTraceTerm φ α (e ρ) = -zetaTraceTerm φ α ρ := by
  have hfun : (fun t : ℝ => φ t⁻¹) = (fun t : ℝ => -φ t) := by
    funext t
    exact hodd t
  have hM : ∀ s : ℂ, mellin φ (-s) = -mellin φ s := by
    intro s
    calc
      mellin φ (-s) = mellin (fun t : ℝ => φ t⁻¹) s :=
        (mellin_comp_inv φ s).symm
      _ = mellin (fun t : ℝ => -φ t) s := by rw [hfun]
      _ = -(mellin φ s) := by
        simpa using (mellin_const_smul φ s (-1 : ℂ))
  intro ρ
  simp only [zetaTraceTerm]
  have harg : (e ρ).val - 1 / 2 = -((ρ : ℂ) - 1 / 2) := by
    rw [hcenter]
    ring
  rw [harg, hM]
  have ho := hmult ρ
  rw [ho]
  ring
