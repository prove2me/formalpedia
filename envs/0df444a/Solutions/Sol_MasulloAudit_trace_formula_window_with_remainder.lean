-- Prove2me | solution 1 for MasulloAudit.trace_formula_window_with_remainder
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:16:36.476177+00:00
-- url     : https://prove2.me/submissions/fefbecd8-d380-4c8b-a8a3-b25ec5a43afd

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

/-- The window `1/2 + (-α, α)` sits inside the full critical strip. -/
private def windowEquiv (α : ℝ) :
    ZetaZerosInTraceStrip α ≃
      {ρ : ZetaZerosInTraceStrip (1 / 2) // |(ρ : ℂ).re - 1 / 2| < α} where
  toFun ρ := ⟨⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1,
    abs_sub_lt_iff.2 ⟨by linarith [ρ.2.2.2.1], by linarith [ρ.2.2.1]⟩⟩, ρ.2.2.2.2⟩
  invFun ρ := ⟨ρ.1.1, ρ.1.2.1, ρ.1.2.2.1, ρ.1.2.2.2.1, ρ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem solution (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    Summable (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) -
        ∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ := by
  intro remainder
  obtain ⟨hI, hP, hZ, hEq⟩ := trace_formula_rational_full_strip φ hφ
  set f := zetaTraceTerm φ (1 / 2)
  let W : Set (ZetaZerosInTraceStrip (1 / 2)) := {ρ | |(ρ : ℂ).re - 1 / 2| < α}
  have hWc : Wᶜ = remainder := by
    ext ρ; simp [W, remainder]
  have hwin : ∀ ρ : ZetaZerosInTraceStrip α,
      zetaTraceTerm φ α ρ = (fun x : W => f x) (windowEquiv α ρ) := fun _ => rfl
  have hWs : Summable (fun x : W => f x) := hZ.subtype W
  have hRs : Summable (fun ρ : remainder => f ρ) := hWc ▸ hZ.subtype Wᶜ
  have hZα : Summable (zetaTraceTerm φ α) := by
    rw [show zetaTraceTerm φ α = (fun x : W => f x) ∘ windowEquiv α from funext hwin]
    exact (windowEquiv α).summable_iff.2 hWs
  have hsumα : (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) = ∑' x : W, f x := by
    simp_rw [hwin]; exact (windowEquiv α).tsum_eq (fun x : W => f x)
  have hsplit := hZ.tsum_subtype_add_tsum_subtype_compl W
  rw [hWc] at hsplit
  refine ⟨hI, hP, hZα, hRs, ?_⟩
  rw [hEq, hsumα, ← hsplit]
  ring

#print axioms solution
