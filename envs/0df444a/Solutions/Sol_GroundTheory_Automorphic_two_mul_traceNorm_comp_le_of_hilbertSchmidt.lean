-- Prove2me | solution 1 for GroundTheory.Automorphic.two_mul_traceNorm_comp_le_of_hilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:59.550933+00:00
-- url     : https://prove2.me/submissions/b9a8169e-995f-475c-985b-f2526d693b91

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_enorm_inner_le
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_adjoint
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_comp_right_le
import Theorems.Thm_GroundTheory_Automorphic_hsNormSq_eq_tsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution (A : K →L[ℂ] H) (B : H →L[ℂ] K) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]
end GroundTheory.Automorphic
