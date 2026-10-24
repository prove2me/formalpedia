-- Prove2me | solution 1 for OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T13:59:46.063992+00:00
-- url     : https://prove2.me/submissions/534227bb-208f-419d-b6be-bc1b9bcf7828

import Mathlib
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_SobolevProof_ae_const_of_weak_derivative_zero

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


lemma primitive_weak_derivative {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = -(∫ x, g x * φ x) := by
  obtain ⟨R,hR,hRs⟩ := hφc.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hs : tsupport φ ⊆ Ioo (-R) R := by
    intro x hx
    have hh := hRs hx
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt,mem_Ioo] using hh
  have hzero : φ (-R) = 0 ∧ φ R = 0 := by
    constructor <;> apply image_eq_zero_of_notMem_tsupport <;>
      intro h <;> have := hs h <;> simp_all
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hgi := locallyIntegrable_intervalIntegrable hg (-R) R
  have h0 : (0 : ℝ) ∈ uIcc (-R) R := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hF : AbsolutelyContinuousOnInterval F (-R) R :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral h0
  have hφa : AbsolutelyContinuousOnInterval φ (-R) R :=
    (hφ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hfd : ∀ᵐ x, x ∈ uIcc (-R) R → deriv F x = g x := by
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hmem
    exact (hx hmem 0 h0).deriv
  have he := hF.integral_mul_deriv_eq_deriv_mul hφa
  rw [hzero.1,hzero.2,mul_zero,mul_zero,sub_self,zero_sub] at he
  have hi : (∫ x in (-R)..R, deriv F x * φ x) = ∫ x in (-R)..R, g x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfd] with x hx hmem
    rw [hx (uIoc_subset_uIcc hmem)]
  rw [hi] at he
  have hleft : Function.support (fun x ↦ F x * deriv φ x) ⊆ Ioc (-R) R := by
    intro x hx
    have hd : x ∈ tsupport (deriv φ) :=
      subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)
    exact Ioo_subset_Ioc_self (hs (tsupport_deriv_subset hd))
  have hright : Function.support (fun x ↦ g x * φ x) ⊆ Ioc (-R) R := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)))
  rwa [intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at he

/-- The precise one-dimensional Sobolev representative, obtained from the weak derivative
without assuming any pointwise regularity or adding a representative to the domain. -/
lemma weak_derivative_representation_oai {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = -(∫ x, g x * φ x)) :
    ∃ c : ℝ, f =ᵐ[volume] fun x ↦ c + ∫ t in (0 : ℝ)..x, g t := by
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hFc : Continuous F := intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hg) 0
  obtain ⟨c,hc⟩ := ae_const_of_weak_derivative_zero (hf.sub hFc.locallyIntegrable) (fun φ hφ hφc ↦ by
    have hi₁ : Integrable (fun x ↦ f x * deriv φ x) volume :=
      hf.integrable_smul_right_of_hasCompactSupport (hφ.continuous_deriv (by simp)) hφc.deriv
    have hi₂ : Integrable (fun x ↦ F x * deriv φ x) volume :=
      hFc.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hφc.deriv
    simp only [Pi.sub_apply,sub_mul,integral_sub hi₁ hi₂,hw φ hφ hφc]
    change -(∫ x, g x * φ x) - (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = 0
    rw [primitive_weak_derivative hg φ hφ hφc,sub_self])
  refine ⟨c,?_⟩
  filter_upwards [hc] with x hx
  exact sub_eq_iff_eq_add.mp hx

end SharpLiebThirring.SobolevProof

end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation_oai := @OAI.SharpLiebThirring.SobolevProof.weak_derivative_representation_oai
