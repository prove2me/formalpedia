-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.chE_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:21:27.365848+00:00
-- url     : https://prove2.me/submissions/9a56947a-9811-487a-aa8a-55e8599e63a0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_trace_eq_inner

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
theorem _root_.solution (k : ℝ) (g : EuclideanSpace ℂ (Fin m × Fin n) → ℂ) :
    chE k (g ∘ matEquiv m n) = (fun y => chirp k y * g y) ∘ matEquiv m n := by
  funext u
  simp only [chE, Function.comp, chirp, trace_eq_inner]
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
