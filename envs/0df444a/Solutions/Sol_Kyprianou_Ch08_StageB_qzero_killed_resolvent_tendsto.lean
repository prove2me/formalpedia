-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_killed_resolvent_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T03:16:31.991803+00:00
-- url     : https://prove2.me/submissions/47a5341d-5352-4a56-99f2-c7d7d76aeacd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_two_sided_occupation_sections_measurable
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open scoped Topology
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
set_option maxHeartbeats 1000000 in
/-- Resolvent-side sequential limit for the zero-discount occupation identity. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        Tendsto
          (fun n : ℕ =>
            ∫⁻ t : ℝ≥0,
              ENNReal.ofReal
                (Real.exp (-(((n : ℝ) + 1)⁻¹) * (t : ℝ))) *
                P {ω | (t : WithTop ℝ≥0) <
                  min (tauMinus (shifted D.X x) 0 ω)
                    (tauPlus (shifted D.X x) a ω) ∧
                  shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)
          atTop
          (𝓝 (∫⁻ t : ℝ≥0,
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue)) := by
  intro Ω mΩ P hP D ψ W hψ hW a x ha hx hxa A hA
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hqseq_tendsto : Tendsto qseq atTop (𝓝 0) := by
    simpa [qseq, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
  have hqseq_antitone : Antitone qseq := by
    intro m n hmn
    dsimp [qseq]
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hmn
    simpa [one_div] using
      (one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1) hmn')
  let E : ℝ≥0 → Set Ω := fun t =>
    {ω | (t : WithTop ℝ≥0) < min (tauMinus (shifted D.X x) 0 ω)
      (tauPlus (shifted D.X x) a ω) ∧ shifted D.X x t ω ∈ A}
  let F : ℕ → ℝ≥0 → ENNReal := fun n t =>
    ENNReal.ofReal (Real.exp (-(qseq n) * (t : ℝ))) * P (E t)
  let F0 : ℝ≥0 → ENNReal := fun t => P (E t)
  have hF_mono : ∀ t : ℝ≥0, Monotone (fun n : ℕ => F n t) := by
    intro t m n hmn
    dsimp [F]
    have hexp : ENNReal.ofReal (Real.exp (-(qseq m) * (t : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-(qseq n) * (t : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmul : qseq n * (t : ℝ) ≤ qseq m * (t : ℝ) :=
        mul_le_mul_of_nonneg_right (hqseq_antitone hmn) (NNReal.coe_nonneg t)
      nlinarith
    exact mul_le_mul_of_nonneg_right hexp (by simp)
  have hF_tendsto : ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ => F n t) atTop (𝓝 (F0 t)) := by
    intro t
    have harg : Tendsto (fun n : ℕ => -(qseq n) * (t : ℝ)) atTop (𝓝 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hqseq_tendsto.const_mul (-(t : ℝ)))
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(qseq n) * (t : ℝ)))
        atTop (𝓝 1) := by
      simpa [Function.comp_def] using
        Real.continuous_exp.continuousAt.tendsto.comp harg
    have heofReal : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(qseq n) * (t : ℝ))))
        atTop (𝓝 1) := by
      simpa [Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hexp
    have hfin : P (E t) ≠ ⊤ := measure_ne_top P (E t)
    dsimp [F, F0]
    simpa [Function.comp_def] using
      ENNReal.Tendsto.mul_const heofReal (Or.inr hfin)
  have hF_meas : ∀ n, AEMeasurable (F n) positiveTimeLebesgue := by
    have hE_meas : Measurable (fun t : ℝ≥0 => P (E t)) := by
      simpa [E] using
        (qzero_killed_two_sided_occupation_sections_measurable
          Ω P D ψ hψ a x ha hx hxa A hA)
    intro n
    dsimp [F]
    have hweight : Measurable (fun t : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(qseq n) * (t : ℝ)))) := by
      measurability
    exact (hweight.mul hE_meas).aemeasurable
  have hRHSlim :
      Tendsto (fun n : ℕ => ∫⁻ t : ℝ≥0, F n t ∂positiveTimeLebesgue) atTop
        (𝓝 (∫⁻ t : ℝ≥0, F0 t ∂positiveTimeLebesgue)) :=
    MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hF_meas
      (Eventually.of_forall hF_mono) (Eventually.of_forall hF_tendsto)
  simpa [F, F0, E, qseq] using hRHSlim
