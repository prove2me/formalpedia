-- Prove2me | solution 1 for OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:59:37.062717+00:00
-- url     : https://prove2.me/submissions/796fca85-822a-4c59-9be8-3b4dac3917da

import Mathlib

section
-- module Solutions.OAIQW_LiebThirring.SobolevProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff

/-- A locally integrable function whose distributional derivative vanishes is constant.
This uses only smooth compact tests, hence applies to the H¹ definition. -/
lemma ae_const_of_weak_derivative_zero_oai {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = 0) : ∃ c : ℝ, f =ᵐ[volume] fun _ ↦ c := by
  have hc (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
      ∀ x y : ℝ, (ρ ⋆[lsmul ℝ ℝ, volume] f) x = (ρ ⋆[lsmul ℝ ℝ, volume] f) y := by
    have hder (x : ℝ) : HasDerivAt (ρ ⋆[lsmul ℝ ℝ, volume] f) 0 x := by
      have hd := hρc.hasDerivAt_convolution_left (lsmul ℝ ℝ) (hρ.of_le (by simp)) hf x
      have ht := hw (fun y ↦ ρ (x-y)) (hρ.comp (contDiff_const.sub contDiff_id))
        (hρc.comp_homeomorph (Homeomorph.subLeft x))
      have hdφ (y : ℝ) : deriv (fun y ↦ ρ (x-y)) y = -deriv ρ (x-y) := by
        simpa only [Function.comp_def, zero_sub, mul_neg, mul_one] using
          ((hρ.differentiable (by simp) (x-y)).hasDerivAt.comp y
            ((hasDerivAt_const y x).sub (hasDerivAt_id y))).deriv
      simp_rw [hdφ,mul_neg,integral_neg] at ht
      have hz : ((deriv ρ ⋆[lsmul ℝ ℝ, volume] f) x) = 0 := by
        rw [convolution_eq_swap]
        simpa only [lsmul_apply,smul_eq_mul,mul_comm,neg_eq_zero] using ht
      rwa [hz] at hd
    exact is_const_of_deriv_eq_zero (fun x ↦ (hder x).differentiableAt)
      (fun x ↦ (hder x).deriv)
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n ↦
    ⟨(n+1 : ℝ)⁻¹,2*(n+1 : ℝ)⁻¹,by positivity,by nlinarith [inv_pos.mpr (show (0 : ℝ)<n+1 by positivity)]⟩
  have hb : Tendsto (fun n ↦ (b n).rOut) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ ↦ (n+1 : ℝ)⁻¹) atTop (𝓝 0) :=
      by simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero] using ht.const_mul 2
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := b) hb (K := 2) (Eventually.of_forall (fun _ ↦ le_refl _)) hf
  obtain ⟨x₀,hx₀⟩ := ha.exists
  refine ⟨f x₀,?_⟩
  filter_upwards [ha] with x hx
  apply tendsto_nhds_unique hx
  convert hx₀ using 1
  funext n
  exact hc ((b n).normed volume) (b n).contDiff_normed (b n).hasCompactSupport_normed x x₀


end SharpLiebThirring.SobolevProof

end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero_oai := @OAI.SharpLiebThirring.SobolevProof.ae_const_of_weak_derivative_zero_oai
