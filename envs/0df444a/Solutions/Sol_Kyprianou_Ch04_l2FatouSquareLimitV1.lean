-- Prove2me | solution 1 for Kyprianou.Ch04.l2FatouSquareLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:38:07.47197+00:00
-- url     : https://prove2.me/submissions/6a3287f0-18c5-463e-adc8-e19abff0442d

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Fatou's inequality for an almost sure limit of square-integrable random variables. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n, Measurable (f n)) (hfi : ∀ n, Integrable (fun ω => (f n ω)^2) P)
    (hgi : Integrable (fun ω => (g ω)^2) P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hlim : Tendsto (fun n => ∫ ω, (f n ω)^2 ∂P) atTop (𝓝 K)) :
    (∫ ω, (g ω)^2 ∂P) ≤ K := by
  have hp : (fun ω => ENNReal.ofReal ((g ω)^2)) =ᵐ[P]
      fun ω => liminf (fun n => ENNReal.ofReal ((f n ω)^2)) atTop := by
    filter_upwards [hae] with ω hω
    exact ((ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)).liminf_eq.symm
  have hfat := lintegral_liminf_le (μ := P) (u := atTop)
    (fun n => ENNReal.measurable_ofReal.comp ((hf n).pow_const 2))
  have hright : (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω)^2) ∂P) =
      fun n => ENNReal.ofReal (∫ ω, (f n ω)^2 ∂P) := by
    funext n
    exact (ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall fun _ => sq_nonneg _)).symm
  change (∫⁻ ω, liminf (fun n => ENNReal.ofReal ((f n ω)^2)) atTop ∂P) ≤
    liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω)^2) ∂P) atTop at hfat
  rw [hright] at hfat
  have hlim' := (ENNReal.continuous_ofReal.tendsto K).comp hlim
  have hle : ENNReal.ofReal (∫ ω, (g ω)^2 ∂P) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun _ => sq_nonneg _),
      lintegral_congr_ae hp]
    exact hfat.trans_eq hlim'.liminf_eq
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hle
