-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.pairing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:21:28.122965+00:00
-- url     : https://prove2.me/submissions/83c9b0e8-a751-4ddb-85cd-57cab203659b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_trace_eq_inner
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_unitMul_apply

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
theorem _root_.solution (s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (u v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re =
      ‖s‖ * inner ℝ (matEquiv m n u) (unitMul _ (s / ‖s‖) hω (matEquiv m n v)) := by
  have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
  have hi : ∀ x y : EuclideanSpace ℂ (Fin m × Fin n), inner ℝ x y = (inner ℂ x y).re := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inner, RCLike.inner_apply, mul_comm]
  rw [hi, unitMul_apply, inner_smul_right, trace_eq_inner, ← Complex.re_ofReal_mul]
  congr 1
  field_simp
end GlobalTheory.CompanionTheory.Kloc.Fresnel
