-- Prove2me | solution 1 for GlobalTheory.MatrixGaussian.gaussian_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:44.867855+00:00
-- url     : https://prove2.me/submissions/86adb4fa-10f4-48b8-91cc-c3a10b6862f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart
import Theorems.Thm_GlobalTheory_MatrixGaussian_exp_diagonal

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
open GlobalTheory GlobalTheory.MatrixGaussian
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MatrixGaussian
theorem _root_.solution (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by
  have hb : ∀ i, 0 < ((π : ℂ) * d i).re := fun i => by
    simpa using mul_pos Real.pi_pos (hd i)
  simp only [exp_diagonal]
  constructor
  · refine Integrable.fintype_prod (f := fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)) fun i => ?_
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (hb i) 0 0
  · rw [integral_fintype_prod_volume_eq_prod (fun i (w : ℂ) => cexp (-(π * d i) * (‖w‖ : ℂ) ^ 2)),
      det_diagonal, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (hb i), Complex.finrank_real_complex]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have : ((2 : ℕ) : ℂ) / 2 = 1 := by norm_num
    rw [this, cpow_one, div_mul_cancel_left₀ hπ]
end GlobalTheory.MatrixGaussian
