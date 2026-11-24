-- Prove2me | solution 1 for GlobalTheory.PluriTaylor.taylor_levi_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:44.763574+00:00
-- url     : https://prove2.me/submissions/95b1ee63-ef19-4947-971c-ec373dac6815

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
import Theorems.Thm_GlobalTheory_PluriTaylor_sum_re_im_eq
import Theorems.Thm_GlobalTheory_PluriTaylor_sum_I_eq
import Theorems.Thm_GlobalTheory_PluriTaylor_re_holomorphicLinearTaylorCoeff_sum_eq
import Theorems.Thm_GlobalTheory_PluriTaylor_re_holomorphicQuadraticTaylorCoeff_sum_eq
import Theorems.Thm_GlobalTheory_PluriTaylor_taylor_two_unif
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LocalMaximumSecondDerivative_leviV_re_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PluriTaylor
open Complex
namespace GlobalTheory.PluriTaylor
theorem _root_.solution : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U →
    IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K,
      closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧
        ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re +
          (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  intro n U K φ η hU hK hKU hφ hη
  obtain ⟨δ, hδ, hT⟩ := taylor_two_unif U K φ η hU hK hKU hφ hη
  refine ⟨δ, hδ, fun z hz => ⟨(hT z hz).1, ?_⟩⟩
  have hp : ∀ j : Fin n, Differentiable ℂ (fun w : V n => w j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable
  refine ⟨fun w => ∑ j, w j * lc (fderiv ℝ φ z) j +
      ∑ j, ∑ k, w j * w k * qc (fderiv ℝ (fderiv ℝ φ) z) j k, ?_, ?_, fun w hw => ?_⟩
  · fun_prop
  · simp
  · have hcd : ContDiffAt ℝ 2 φ z := hφ.contDiffAt (hU.mem_nhds (hKU hz))
    have h1 := re_holomorphicLinearTaylorCoeff_sum_eq (fderiv ℝ φ z) (fun j => (w j).re) (fun j => (w j).im)
    have h2 := re_holomorphicQuadraticTaylorCoeff_sum_eq (fderiv ℝ (fderiv ℝ φ) z) (fun j => (w j).re) (fun j => (w j).im)
    have h3 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq hcd (fun j => w j)
    simp only [Complex.re_add_im, sum_re_im_eq, sum_I_eq] at h1 h2 h3
    have h4 := (hT z hz).2 w hw
    simp only [Complex.add_re]
    linarith
end GlobalTheory.PluriTaylor
