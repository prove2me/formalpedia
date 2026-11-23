-- Prove2me | solution 1 for GlobalTheory.RealWeil.proj_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:09.417891+00:00
-- url     : https://prove2.me/submissions/409fd2bf-d9c6-4cc0-9ddb-c51162772cea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Theorems.Thm_GlobalTheory_RealWeil_proj_apply
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
variable {J : V ≃ₗᵢ[ℝ] V}
namespace GlobalTheory.RealWeil
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (w : V) :
    proj h (ρ (-w) f) = ρ (-w) (𝓕 (fun u => gau u • ρ u f) (J w)) := by
  rw [proj_apply, Real.fourier_eq', ← ContinuousLinearMap.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_smul, h.2.1, smul_smul]
    rw [add_comm (-w) u, omJ_skew hJ u (-w)]
    congr 1
    have e : omJ J u (-w) = -⟪u, J w⟫ := by simp [omJ]
    rw [e, mul_right_comm _ (gau u), ← Complex.exp_add, mul_comm]
    congr 2
    push_cast
    ring
  · have := (Real.fourierIntegral_convergent_iff (J w)).2 (h.integrable f)
    simpa only [Circle.smul_def, Real.fourierChar_apply, mul_neg, neg_mul, Complex.ofReal_neg] using this
end GlobalTheory.RealWeil
