-- Prove2me | solution 1 for GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:07.403563+00:00
-- url     : https://prove2.me/submissions/f3de06a4-abcd-45db-b28b-274cacabb052

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplaceIntegralEntireBoundedInVerticalStrips
import Theorems.Thm_GlobalTheory_LaplaceStrip_norm_integrand
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.LaplaceStrip
namespace GlobalTheory.LaplaceStrip
theorem _root_.solution {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr
end GlobalTheory.LaplaceStrip
