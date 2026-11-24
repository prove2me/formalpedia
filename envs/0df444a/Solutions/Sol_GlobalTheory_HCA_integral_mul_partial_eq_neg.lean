-- Prove2me | solution 1 for GlobalTheory.HCA.integral_mul_partial_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:25.969459+00:00
-- url     : https://prove2.me/submissions/9c9ce8af-ad26-4233-b4be-ece615ca4839

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
import Theorems.Thm_GlobalTheory_HCA_integrable_mul_of_tsupport_subset
import Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (j : Fin d)
    {u ψ : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x (ev j) = - ∫ x, fderiv ℝ u x (ev j) * ψ x := by
  have hu1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (ev j)) U :=
    contDiffOn_dw_of_isOpen hU [j] u hu
  have hψ1 : Continuous (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsub : tsupport (fun x => fderiv ℝ ψ x (ev j)) ⊆ tsupport ψ := by
    refine (closure_mono ?_).trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := ψ))
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; exact hx (by simp [h])
  have hψ1c : HasCompactSupport (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E d →L[ℝ] ℂ => L (ev j)) (by simp)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_of_tsupport_subset hU hu1.continuousOn hψ.continuous hψc hψs
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ1 hψ1c (hsub.trans hψs)
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ.continuous hψc hψs
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hψs hx))).differentiableAt (by simp)
  · intro x _
    exact hψ.differentiable (by simp) x
end GlobalTheory.HCA
