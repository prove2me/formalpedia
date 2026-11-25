-- Prove2me | solution 1 for GlobalTheory.RealWeil.exists_norm_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:39.725715+00:00
-- url     : https://prove2.me/submissions/d5e5897b-346f-4c51-8fa2-22668c54f07e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_besselOp_mem
import Theorems.Thm_GlobalTheory_RealWeil_fourierInv_besselOp_pow
import Theorems.Thm_GlobalTheory_RealWeil_exists_norm_toLp_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution :
    ∃ A ∈ weylAlg l, ∀ (f : Sch l) (x : EuclideanSpace ℝ l), ‖f x‖ ≤ ‖(A f).toLp 2 volume‖ := by
  obtain ⟨N, C, hC, h⟩ := exists_norm_toLp_one_le (l := l)
  refine ⟨(C : ℂ) • besselOp l ^ N, Subalgebra.smul_mem _ (pow_mem besselOp_mem _) _, fun f x => ?_⟩
  have h1 := norm_fourier_apply_le_toLp_one (𝓕⁻ f) x
  rw [FourierTransform.fourier_fourierInv_eq] at h1
  refine h1.trans ((h _).trans (le_of_eq ?_))
  rw [← fourierInv_besselOp_pow, ← norm_fourier_toL2_eq, FourierTransform.fourier_fourierInv_eq,
    ContinuousLinearMap.smul_apply, ← toLpCLM_apply (𝕜 := ℂ), ← toLpCLM_apply (𝕜 := ℂ), map_smul, norm_smul,
    norm_real, Real.norm_of_nonneg hC]
end GlobalTheory.RealWeil
