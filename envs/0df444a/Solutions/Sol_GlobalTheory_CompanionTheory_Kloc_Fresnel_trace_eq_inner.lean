-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.trace_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:42.998971+00:00
-- url     : https://prove2.me/submissions/7b99a4f4-f2d3-40fb-9f9d-ff5729200ce6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_matEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (u v : Fin m → Fin n → ℂ) :
    Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) = inner ℂ (matEquiv m n u) (matEquiv m n v) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type_right]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    matEquiv_apply, RCLike.inner_apply, mul_comm]
  rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
