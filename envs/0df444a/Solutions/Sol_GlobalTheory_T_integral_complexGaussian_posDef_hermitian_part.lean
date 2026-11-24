-- Prove2me | solution 1 for GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:14:59.553842+00:00
-- url     : https://prove2.me/submissions/6fa716b8-5b8f-4359-b749-6280fcadbafb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Theorems.Thm_GlobalTheory_MatrixGaussian_integral_gaussian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), (A + Aᴴ).PosDef → A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧ ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  first | exact @GlobalTheory.MatrixGaussian.integral_gaussian | exact GlobalTheory.MatrixGaussian.integral_gaussian | (intros; apply GlobalTheory.MatrixGaussian.integral_gaussian <;> assumption)
end _root_.GlobalTheory.T
