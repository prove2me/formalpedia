-- Prove2me | solution 1 for MasulloRH.trace_formula_inversion_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T13:36:25.574198+00:00
-- url     : https://prove2.me/submissions/2ebc33a1-26a3-4998-a522-fef26b3d260b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloAudit_trace_formula_rational_of_half_le
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloRH_even_test_omitted_sum_eq_four_mul_upper_right
import Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero
import Mathlib

set_option autoImplicit false

namespace MasulloRH_EvenReduction

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff

private lemma test_comp_clm {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ)
    (L : ℂ →L[ℝ] ℂ) : MasulloRH.IsRationalTraceTest (L ∘ φ) := by
  rcases hφ with ⟨hSmooth, hCpt, hSupp, hOne⟩
  refine ⟨L.contDiff.comp hSmooth, hCpt.comp_left (map_zero L), ?_, ?_⟩
  · exact (tsupport_comp_subset (map_zero L) φ).trans hSupp
  · show L (φ 1) = 0
    rw [hOne, map_zero]

private lemma test_mellinConvergent {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  rcases hφ with ⟨hSmooth, hCpt, hSupp, _⟩
  unfold MellinConvergent
  simp only [smul_eq_mul]
  have hg_cont : Continuous (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : 0 < x
    · exact (Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr (ne_of_gt hx))).mul
        hSmooth.continuous.continuousAt
    · have hx_not_supp : x ∉ tsupport φ := fun hmem => hx (hSupp hmem)
      have h_zero : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx_not_supp
      have hg_zero : (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
        h_zero.mono (fun y (hy : φ y = 0) => by dsimp; rw [hy, mul_zero])
      exact continuousAt_const.congr hg_zero.symm
  have hg_cpt : HasCompactSupport (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) :=
    hCpt.mul_left
  exact (hg_cont.integrable_of_hasCompactSupport hg_cpt).integrableOn

private lemma test_mellin_re_add_im {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ) (s : ℂ) :
    mellin φ s = mellin (fun t => ((φ t).re : ℂ)) s + Complex.I * mellin (fun t => ((φ t).im : ℂ)) s := by
  have hφ_re : MasulloRH.IsRationalTraceTest (fun t => ((φ t).re : ℂ)) :=
    test_comp_clm hφ (Complex.ofRealCLM.comp Complex.reCLM)
  have hφ_im : MasulloRH.IsRationalTraceTest (fun t => ((φ t).im : ℂ)) :=
    test_comp_clm hφ (Complex.ofRealCLM.comp Complex.imCLM)
  have hInt_re : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((φ t).re : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using test_mellinConvergent hφ_re s
  have hInt_im : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((φ t).im : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using test_mellinConvergent hφ_im s
  simp only [mellin, smul_eq_mul]
  have hdecomp : (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) =
      (fun t : ℝ =>
        (t : ℂ) ^ (s - 1) * ((φ t).re : ℂ) +
          Complex.I * ((t : ℂ) ^ (s - 1) * ((φ t).im : ℂ))) := by
    funext t
    conv_lhs => rw [← Complex.re_add_im (φ t)]
    ring
  rw [hdecomp, MeasureTheory.integral_add hInt_re (hInt_im.const_mul Complex.I),
      MeasureTheory.integral_const_mul]

end MasulloRH_EvenReduction

open MasulloRH MeasureTheory Set

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (heven : ∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  by_cases hα_half : 1 / 2 ≤ α
  · exact MasulloAudit.trace_formula_rational_of_half_le α hα_half φ hφ
  · have hα_lt : α < 1 / 2 := lt_of_not_ge hα_half
    have hWin := MasulloAudit.trace_formula_window_with_remainder α φ hφ
    rcases hWin with ⟨hInt, hSumP, hSumZ, _, hEq⟩
    refine ⟨hInt, hSumP, hSumZ, ?_⟩
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    suffices hRemZero : (∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ) = 0 by
      rw [hRemZero, sub_zero] at hEq
      exact hEq
    let ψ_re : ℝ → ℝ := fun t => (φ t).re
    let ψ_im : ℝ → ℝ := fun t => (φ t).im
    let φ_re : ℝ → ℂ := fun t => (ψ_re t : ℂ)
    let φ_im : ℝ → ℂ := fun t => (ψ_im t : ℂ)
    have hφ_re : IsRationalTraceTest φ_re :=
      MasulloRH_EvenReduction.test_comp_clm hφ (Complex.ofRealCLM.comp Complex.reCLM)
    have hφ_im : IsRationalTraceTest φ_im :=
      MasulloRH_EvenReduction.test_comp_clm hφ (Complex.ofRealCLM.comp Complex.imCLM)
    have heven_re : ∀ t : ℝ, 0 < t → ψ_re t⁻¹ = ψ_re t :=
      fun t ht => congrArg Complex.re (heven t ht)
    have heven_im : ∀ t : ℝ, 0 < t → ψ_im t⁻¹ = ψ_im t :=
      fun t ht => congrArg Complex.im (heven t ht)
    have hSumRem_re : Summable (fun ρ : remainder => zetaTraceTerm φ_re (1 / 2) ρ) :=
      (MasulloAudit.trace_formula_window_with_remainder α φ_re hφ_re).2.2.2.1
    have hSumRem_im : Summable (fun ρ : remainder => zetaTraceTerm φ_im (1 / 2) ρ) :=
      (MasulloAudit.trace_formula_window_with_remainder α φ_im hφ_im).2.2.2.1
    have hTerm_decomp : (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) =
        (fun ρ : remainder =>
          zetaTraceTerm φ_re (1 / 2) ρ + Complex.I * zetaTraceTerm φ_im (1 / 2) ρ) := by
      funext ρ
      dsimp [zetaTraceTerm]
      rw [MasulloRH_EvenReduction.test_mellin_re_add_im hφ ((ρ : ℂ) - 1 / 2)]
      ring
    rw [hTerm_decomp, hSumRem_re.tsum_add (hSumRem_im.mul_left Complex.I), tsum_mul_left]
    have hSymm_re := (MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right α hα ψ_re hφ_re heven_re).2
    have hSymm_im := (MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right α hα ψ_im hφ_im heven_im).2
    have hChild_re := MasulloRH.even_real_upper_right_omitted_sum_zero α hα hα_lt ψ_re hφ_re heven_re
    have hChild_im := MasulloRH.even_real_upper_right_omitted_sum_zero α hα hα_lt ψ_im hφ_im heven_im
    rw [hSymm_re, hChild_re, hSymm_im, hChild_im]
    simp
