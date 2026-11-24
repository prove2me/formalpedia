-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:40.211864+00:00
-- url     : https://prove2.me/submissions/1cbaa087-6b5d-41a8-b196-cb86eb21f45e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_integrable_gauss
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_differentiable_dilated
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_continuous_dilated
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_eventually_small
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_norm_dilated_le
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_integral_step
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
theorem _root_.solution (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ)
    (hK : Continuous K) (hK1 : ∀ v, ‖K v‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hcm : ∀ (c : ℂ) (f : ℂ → ℂ) (r : ℕ),
      iteratedDeriv r (fun w => c * f w) = fun w => c * iteratedDeriv r f w := by
    intro c f r
    induction r with
    | zero => simp only [iteratedDeriv_zero]
    | succ r ih => rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_small m n X)
  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have hd : ∀ v : Fin m → Fin n → ℂ,
      DifferentiableOn ℂ (fun z => K v * dilated m n X v z) (Metric.ball (0 : ℂ) ρ) :=
    fun v => ((differentiable_dilated m n X v).const_mul (K v)).differentiableOn
  have hm : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      AEStronglyMeasurable (fun v : Fin m → Fin n → ℂ => K v * dilated m n X v z) volume :=
    fun z _ => (hK.mul (continuous_dilated m n X z)).aestronglyMeasurable
  have hb : ∀ z₀ ∈ Metric.ball (0 : ℂ) ρ, ∃ V ∈ 𝓝 z₀, ∃ g : (Fin m → Fin n → ℂ) → ℝ,
      Integrable g volume ∧ ∀ z ∈ V ∩ Metric.ball (0 : ℂ) ρ, ∀ v,
        ‖K v * dilated m n X v z‖ ≤ g v := by
    intro z₀ _
    refine ⟨Set.univ, Filter.univ_mem,
      fun v => 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2),
      (integrable_gauss m n).const_mul 2, ?_⟩
    intro z hz v
    obtain ⟨h1, h2⟩ := hsmall z hz.2
    rw [norm_mul]
    calc ‖K v‖ * ‖dilated m n X v z‖
        ≤ 1 * (2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2)) :=
          mul_le_mul (hK1 v) (norm_dilated_le m n X z h1 h2 v) (norm_nonneg _) zero_le_one
      _ = 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := one_mul _
  have hstep := integral_step (μ := volume) hU (fun z v => K v * dilated m n X v z) hd hm hb
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz
    exact (hstep.1 z hz).differentiableAt.differentiableWithinAt
  · intro r
    have h := iteratedDeriv_integral (μ := volume) hU r (fun z v => K v * dilated m n X v z)
      hd hm hb 0 (Metric.mem_ball_self hρ)
    refine h.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact congrFun (hcm (K v) _ r) 0
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
