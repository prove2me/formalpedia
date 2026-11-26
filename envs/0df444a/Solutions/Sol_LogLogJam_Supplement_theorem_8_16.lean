-- Prove2me | solution 1 for LogLogJam.Supplement.theorem_8_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:30:42.008429+00:00
-- url     : https://prove2.me/submissions/25f5b853-455a-46ec-815e-c498dcbf2106
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LogLogJam_Supplement_weak_success_localization
import Theorems.Thm_LogLogJam_Supplement_constant_confidence_tomography
import Mathlib
import Definitions.Def_LogLogJam_Supplement_IsGaussQP
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open LogLogJam.Supplement
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 / 3 → 0 < δ → δ < 1 →
      ∀ m : ℕ, C * Real.log (1 / δ) / ε ^ 2 ≤ m →
      ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
        (est : Kernel (Fin m → ℝ) (State (Occupation (Fin 1)))),
        (∀ (t : Fin m) (x x' : Fin t → ℝ), S.povm t x = S.povm t x') ∧
        IsMarkovKernel est ∧
        ∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ →
          ENNReal.ofReal (1 - δ) ≤
            ∫⁻ x, est x {σ | IsPureCentGauss σ ∧
                BosonicLearn.traceDist ρ.coefficients σ.coefficients ≤ ENNReal.ofReal ε}
              ∂(BosonicLearn.transcriptLaw S ρ.coefficients) := by
  obtain ⟨A, hA, hstrong⟩ := constant_confidence_tomography
  obtain ⟨c, hc, hweak⟩ := weak_success_localization
  let C := max A c⁻¹
  have hC : 0 < C := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro ε δ hε hε' hδ hδ' m hm
  have hl : 0 < Real.log (1 / δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  by_cases h : δ ≤ 1/2
  · apply hstrong ε δ hε hε' hδ h m
    exact le_trans (by gcongr; exact le_max_left _ _) hm
  have hm' : 0 < (m : ℝ) := lt_of_lt_of_le (by positivity) hm
  obtain ⟨S,est,hS,hest,hacc⟩ := hweak ε hε hε' m (by exact_mod_cast hm')
  refine ⟨S, est, hS, hest, ?_⟩
  intro ρ hρ
  refine (ENNReal.ofReal_le_ofReal ?_).trans (hacc ρ hρ)
  apply le_min (by linarith)
  have hlog : 1 - δ ≤ Real.log (1/δ) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos hδ]
  have hx : c⁻¹ * Real.log (1/δ) ≤ (m:ℝ)*ε^2 :=
    (mul_le_mul_of_nonneg_right (le_max_right A c⁻¹) hl.le).trans
      ((div_le_iff₀ (sq_pos_of_pos hε)).mp hm)
  have hh := mul_le_mul_of_nonneg_left hx hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hh
  linarith
