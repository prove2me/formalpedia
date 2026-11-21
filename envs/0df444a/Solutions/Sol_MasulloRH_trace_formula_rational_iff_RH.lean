-- Prove2me | solution 1 for MasulloRH.trace_formula_rational_iff_RH
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:37:46.020059+00:00
-- url     : https://prove2.me/submissions/5ca8d077-cc8c-4d20-9851-d47db8b710df

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_MasulloRH_omitted_zero_cancellation_iff_RH

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

theorem solution :
    (∀ (α : ℝ), 0 < α → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) ↔
    RiemannHypothesis := by
  constructor
  · -- Restricted formula for every width ⇒ omitted contributions vanish ⇒ RH.
    intro hT
    refine omitted_zero_cancellation_iff_RH.mp ?_
    intro α hα _hα2 φ hφ
    dsimp only
    obtain ⟨-, -, -, hEq⟩ := hT α hα φ hφ
    obtain ⟨-, -, -, -, hW⟩ := trace_window_comparison α φ hφ
    rw [archTerm_log_test_eq_neg_real_place φ hφ] at hW
    linear_combination hW - hEq
  · -- RH ⇒ nothing is omitted from any window of positive width.
    intro hRH α hα φ hφ
    obtain ⟨hI, hP, hZ, -, hW⟩ := trace_window_comparison α φ hφ
    have hempty : IsEmpty
        {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|} := by
      refine ⟨fun r => ?_⟩
      obtain ⟨⟨z, hz0, hzpos, hzlt⟩, hzα⟩ := r
      have hre : z.re = 1 / 2 := by
        refine hRH z hz0 ?_ ?_
        · rintro ⟨n, rfl⟩
          have hn : (0 : ℝ) ≤ n := n.cast_nonneg
          have : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
          rw [this] at hzpos
          linarith
        · rintro rfl
          simp at hzlt
      have hzα' : α ≤ |z.re - 1 / 2| := hzα
      rw [hre, sub_self, abs_zero] at hzα'
      linarith
    have h0 : (∑' r : {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|},
        (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 :=
      tsum_empty
    refine ⟨hI, hP, hZ, ?_⟩
    rw [h0, add_zero, archTerm_log_test_eq_neg_real_place φ hφ] at hW
    linear_combination hW
