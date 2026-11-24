-- Prove2me | solution 1 for GlobalTheory.fourier_prod_coord_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:57.786063+00:00
-- url     : https://prove2.me/submissions/ab8ee760-b06c-4cc8-8e3e-81561403c5c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierProdSingleCoordinateFunctions
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_volume_preserving_ofLp_complex
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
open scoped RealInnerProductSpace FourierTransform
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (I : Type) [Fintype I] (f : I → ℂ → ℂ)
    (_hf : ∀ i, Integrable (f i)) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  simp only [Real.fourier_eq']
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (volume_preserving_ofLp_complex I).integral_comp
      (MeasurableEquiv.toLp 2 (I → ℂ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_mul]
end GlobalTheory
