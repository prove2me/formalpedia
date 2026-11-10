-- Prove2me | solution 1 for KallMayerSLP.SimpleRecourse.lemma_2_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:19:18.969086+00:00
-- url     : https://prove2.me/submissions/45432772-957d-4df1-8ee9-d47e1c51080a

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

open KallMayerSLP.SimpleRecourse in
theorem solution (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : Integrable (fun ξ => ξ) P) (a b : EReal)
    (hI : 0 < P {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}) :
    (∀ z : ℝ, (z : EReal) ≤ a →
      expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z =
        srt α β γ z (∫ ξ, ξ ∂P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}])) ∧
    (∀ z : ℝ, b ≤ (z : EReal) →
      expectedSRT α β γ P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}] z =
        srt α β γ z (∫ ξ, ξ ∂P[|{ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b}])) := by
  obtain ⟨I, hIdef⟩ : ∃ I : Set ℝ, I = {ξ : ℝ | a < (ξ : EReal) ∧ (ξ : EReal) ≤ b} := ⟨_, rfl⟩
  rw [← hIdef] at hI ⊢
  have hIm : MeasurableSet I := by
    rw [hIdef]
    exact (measurableSet_lt measurable_const measurable_coe_real_ereal).inter
      (measurableSet_le measurable_coe_real_ereal measurable_const)
  haveI : IsProbabilityMeasure (P[|I]) := cond_isProbabilityMeasure hI.ne'
  have hQi : Integrable (fun ξ : ℝ => ξ) (P[|I]) := by
    unfold ProbabilityTheory.cond
    exact hP.restrict.smul_measure (ENNReal.inv_ne_top.mpr hI.ne')
  have hmem := ae_cond_mem (μ := P) hIm
  have hone : (P[|I]).real Set.univ = 1 := probReal_univ
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hlt : ∀ᵐ ξ ∂(P[|I]), z < ξ := by
      filter_upwards [hmem] with ξ hξ
      rw [hIdef] at hξ
      exact EReal.coe_lt_coe_iff.mp (lt_of_le_of_lt hz hξ.1)
    have hmean : z ≤ ∫ ξ, ξ ∂(P[|I]) := by
      have := integral_mono_ae (integrable_const z) hQi (hlt.mono fun ξ h => h.le)
      rwa [integral_const, hone, one_smul] at this
    unfold expectedSRT srt
    have hcongr : (fun ξ => α * (ξ - z)⁺ + β * (ξ - z)⁻) =ᵐ[P[|I]] fun ξ => α * ξ - α * z := by
      filter_upwards [hlt] with ξ hξ
      rw [posPart_eq_self.mpr (by linarith), negPart_eq_zero.mpr (by linarith)]
      ring
    rw [integral_congr_ae hcongr, integral_sub (hQi.const_mul α) (integrable_const _),
      integral_const_mul, integral_const, hone, one_smul,
      posPart_eq_self.mpr (by linarith), negPart_eq_zero.mpr (by linarith)]
    ring
  · have hle : ∀ᵐ ξ ∂(P[|I]), ξ ≤ z := by
      filter_upwards [hmem] with ξ hξ
      rw [hIdef] at hξ
      exact EReal.coe_le_coe_iff.mp (le_trans hξ.2 hz)
    have hmean : ∫ ξ, ξ ∂(P[|I]) ≤ z := by
      have := integral_mono_ae hQi (integrable_const z) hle
      rwa [integral_const, hone, one_smul] at this
    unfold expectedSRT srt
    have hcongr : (fun ξ => α * (ξ - z)⁺ + β * (ξ - z)⁻) =ᵐ[P[|I]] fun ξ => β * z - β * ξ := by
      filter_upwards [hle] with ξ hξ
      rw [posPart_eq_zero.mpr (by linarith), negPart_eq_neg.mpr (by linarith)]
      ring
    rw [integral_congr_ae hcongr, integral_sub (integrable_const _) (hQi.const_mul β),
      integral_const_mul, integral_const, hone, one_smul,
      posPart_eq_zero.mpr (by linarith), negPart_eq_neg.mpr (by linarith)]
    rw [integral_const_mul]
    ring
