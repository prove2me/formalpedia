-- Prove2me | solution 1 for LogLogJam.Supplement.split_tomography
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:31:42.040622+00:00
-- url     : https://prove2.me/submissions/c9ab77b2-f2d4-4bb3-87f3-0ff1f6dfbebe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_LogLogJam_Supplement_split_readout_accuracy
import Theorems.Thm_LogLogJam_Supplement_squeezed_decoder
import Theorems.Thm_LogLogJam_Supplement_phase_count_reconstruction

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

open LogLogJam LogLogJam.Supplement

/-- The phase-and-count route to centered pure-state tomography at the
constant-inclusive confidence logarithm of Lemma 8.26. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η^2 ≤ m →
    ∃ (S : AdaptiveScheme 1 m ℝ) (est : (Fin m → ℝ) → State (Occupation (Fin 1))),
      phaseCountReadouts S ∧ Measurable est ∧ (∀ x, IsPureCentGauss (est x)) ∧
      ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
        transcriptLaw S ρ.coefficients
          {x | ENNReal.ofReal (5 * η) < traceDist ρ.coefficients (est x).coefficients} ≤
            ENNReal.ofReal (2 * δ) := by
  obtain ⟨C, hC, hstats⟩ := split_readout_accuracy
  obtain ⟨D, hD, hden, hsurj, hangle, hrad⟩ := squeezed_decoder
  refine ⟨C, hC, ?_⟩
  intro η δ hη hsmall hδ hδone m hm
  obtain ⟨S, a, μ, hS, ha, hμ, hnonneg, _, _, hprob⟩ :=
    hstats η δ hη hsmall hδ hδone m hm
  let est := fun x => D (Real.arsinh (Real.sqrt (μ x)), a x)
  have hpos (x) : 0 ≤ Real.arsinh (Real.sqrt (μ x)) :=
    Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg _)
  have hmeas : Measurable est := hD.comp
    ((Real.continuous_arsinh.measurable.comp (Real.continuous_sqrt.measurable.comp hμ)).prodMk ha)
  refine ⟨S, est, hS, hmeas, fun x => (hden _ _ (hpos x)).2, ?_⟩
  intro ρ hρ
  obtain ⟨r, θ, hr, rfl⟩ := hsurj ρ hρ
  obtain ⟨hang, hcount⟩ := hprob _ _ _ (hden r θ hr).1
  have hang' : transcriptLaw S (D (r, θ)).coefficients
      {x | ENNReal.ofReal η < traceDist (D (r, θ)).coefficients (D (r, a x)).coefficients} ≤
      ENNReal.ofReal δ := by
    refine (measure_mono ?_).trans hang
    intro x hx
    change ENNReal.ofReal η < traceDist (D (r, θ)).coefficients (D (r, a x)).coefficients at hx
    rw [hangle r θ (a x) hr] at hx
    exact lt_of_not_ge (fun h => (not_lt_of_ge (ENNReal.ofReal_le_ofReal h)) hx)
  have hf := phase_count_reconstruction (transcriptLaw S (D (r, θ)).coefficients)
    (D (r, θ)) (fun x => D (r, a x)) est μ hr hη.le hη.le hsmall hnonneg
    hang' hcount (fun x => hrad r _ (a x) hr (hpos x))
  rw [← ENNReal.ofReal_add hδ.le hδ.le,
    show η + 4 * η = 5 * η by ring, show δ + δ = 2 * δ by ring] at hf
  exact hf
