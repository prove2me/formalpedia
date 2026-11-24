-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.kFac_zero_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:24:56.561945+00:00
-- url     : https://prove2.me/submissions/d5d96866-bc4e-4600-ab40-4352be2e5371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution : kFac F 0 * (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) = 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * (-4 * (Real.pi : ℂ) ^ 2) = 1 := by
    rw [inv_pow, mul_pow, mul_pow, I_sq]
    field_simp
    ring
  unfold kFac
  simp only [mul_zero, cpow_zero, mul_one, Finset.prod_const, Finset.card_univ]
  rw [← mul_pow, h1, one_pow]
end GlobalTheory.HeckeTwoExp
