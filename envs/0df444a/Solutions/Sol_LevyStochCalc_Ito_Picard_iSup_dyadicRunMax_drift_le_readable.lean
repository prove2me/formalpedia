-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:27.006097+00:00
-- url     : https://prove2.me/submissions/cba7619a-a1c8-4c13-84b8-0674df25bc44

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
theorem LevyStochCalc.Probability.dyadicTime_nonneg {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) : 0 ≤ dyadicTime T n k :=
  le_min (by positivity) hT
theorem LevyStochCalc.Probability.dyadicTime_le {T : ℝ} (n k : ℕ) : dyadicTime T n k ≤ T := min_le_right _ _
theorem LevyStochCalc.Probability.dyadicTime_mem_Icc {T : ℝ} (hT : 0 ≤ T) (n k : ℕ) :
    dyadicTime T n k ∈ Set.Icc (0 : ℝ) T :=
  ⟨dyadicTime_nonneg hT n k, dyadicTime_le n k⟩
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- A pathwise bound over the window bounds the supremum of the sampled running maxima. -/
theorem LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound {A : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) {ω : Ω} {c : ℝ≥0∞}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ≤ c) :
    (⨆ n, (‖dyadicRunMax A T n ω‖₊ : ℝ≥0∞)) ≤ c := by
  refine iSup_le fun n => ?_
  rw [enorm_dyadicRunMax_readable]
  exact iSup_le fun k => h _ (dyadicTime_mem_Icc hT n (k : ℕ))
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The drift component is dominated over the window by its own total variation there. -/
theorem solution
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T') {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) T') volume) :
    (⨆ m, (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i) T' m ω‖₊ : ℝ≥0∞))
      ≤ (‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) := by
  refine LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound hT' fun t ht => ?_
  have hval : LevyStochCalc.Ito.Picard.picardStep_drift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T' := Set.Icc_subset_Icc le_rfl ht.2
  have hnn' : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T')]
      fun s => ‖coeffs.μ s (X s ω) i‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have hmono : ∫ s in Set.Icc (0 : ℝ) t, ‖coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.setIntegral_mono_set hint.norm hnn' hsub.eventuallyLE
  have hnorm : ‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖
      ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    le_trans (MeasureTheory.norm_integral_le_integral_norm _) hmono
  rw [hval]
  refine le_trans (by rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.mpr (nnnorm_add_le _ _))
    (add_le_add le_rfl ?_)
  have hnn : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ :=
    MeasureTheory.integral_nonneg fun _ => norm_nonneg _
  refine ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp ?_)
  rw [coe_nnnorm, coe_nnnorm,
    show ‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖
        = ∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖ from
      by rw [Real.norm_eq_abs, abs_of_nonneg hnn]]
  exact hnorm
