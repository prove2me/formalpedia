-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_interval_occupation_qzero_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T01:59:27.163348+00:00
-- url     : https://prove2.me/submissions/134c062f-8367-4bcc-9d9c-3dbe6fab4e8a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_interval_occupation_qpos_set_identity
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_denominator_positive
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_q_continuity_and_monotonicity
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_scale_negative_argument_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_density_pointwise_tendsto
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_density_ratio_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_density_uniform_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_density_lintegral_tendsto
import Theorems.Thm_Kyprianou_Ch08_StageB_qzero_killed_resolvent_tendsto
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), q = 0 → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Icc 0 a)).withDensity
      (fun y : ℝ => ENNReal.ofReal (killedIntervalDensity (W q) a x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω)
              (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  subst q
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hqpos_eq : ∀ n : ℕ,
      ((volume.restrict (Set.Icc 0 a)).withDensity
        (fun y : ℝ => ENNReal.ofReal
          (killedIntervalDensity (W (qseq n)) a x y))) A =
      ∫⁻ t : ℝ≥0,
        ENNReal.ofReal (Real.exp (-(qseq n) * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) <
            min (tauMinus (shifted D.X x) 0 ω)
              (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
    intro n
    have hn : 0 < qseq n := by
      dsimp [qseq]
      positivity
    simpa [qseq] using
      (Kyprianou.Ch08.StageB.p2m87_interval_occupation_qpos_set_identity
        Ω P D ψ W hψ hW (qseq n) a x hn ha hx hxa A hA)
  have hden : ∀ b : ℝ, 0 < b → 0 < W 0 b := by
    intro b hb
    exact qzero_scale_denominator_positive Ω P D ψ W hψ hW b hb
  have hs := qzero_scale_q_continuity_and_monotonicity ψ W hW
  have hz := qzero_scale_negative_argument_zero ψ W hW
  have hbound := qzero_killed_density_uniform_bound
    Ω P D ψ W hψ hW hden hs.2 hz
    (fun a x ha hx hxa n y hy =>
      qzero_killed_density_ratio_bound Ω P D ψ W hψ hW hden hs.2
        a x ha hx hxa n y hy)
    a x ha hx hxa
  have hpoint_all :
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ y : ℝ, Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y)) atTop
        (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y))) := by
    intro Ω mΩ P hP D ψ W hψ hW a x ha hx hxa y
    exact qzero_killed_density_pointwise_tendsto Ω P D ψ W hψ hW
      (fun b hb => qzero_scale_denominator_positive Ω P D ψ W hψ hW b hb)
      (qzero_scale_q_continuity_and_monotonicity ψ W hW).1
      (qzero_scale_negative_argument_zero ψ W hW) a x ha hx hxa y
  have hbound_all :
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y) ≤
        ENNReal.ofReal (W 1 x * W 1 a / W 0 a + W 1 x) := by
    intro Ω mΩ P hP D ψ W hψ hW a x ha hx hxa n y hy
    exact qzero_killed_density_uniform_bound Ω P D ψ W hψ hW
      (fun b hb => qzero_scale_denominator_positive Ω P D ψ W hψ hW b hb)
      (qzero_scale_q_continuity_and_monotonicity ψ W hW).2
      (qzero_scale_negative_argument_zero ψ W hW)
      (fun a x ha hx hxa n y hy =>
        qzero_killed_density_ratio_bound Ω P D ψ W hψ hW
          (fun b hb => qzero_scale_denominator_positive Ω P D ψ W hψ hW b hb)
          (qzero_scale_q_continuity_and_monotonicity ψ W hW).2
          a x ha hx hxa n y hy)
      a x ha hx hxa n y hy
  have hL := qzero_density_lintegral_tendsto
    Ω P D ψ W hψ hW hpoint_all hbound_all a x ha hx hxa A hA
  have hR := qzero_killed_resolvent_tendsto
    Ω P D ψ W hψ hW a x ha hx hxa A hA
  exact tendsto_nhds_unique hL (by
    simpa [qseq] using
      (hR.congr' (Eventually.of_forall (fun n => (hqpos_eq n).symm))))
