-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.norm_phi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:23:14.977712+00:00
-- url     : https://prove2.me/submissions/358d43f6-6d11-4d3d-a835-643c52cbf7bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeWeightTwoLatticeSum
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace GlobalTheory.HeckeTwo
theorem _root_.solution (σ w : ℂ) (hσ : 0 < σ.re) (c : ℝ) (hc : 0 < c) (hcw : c ≤ |w.im|) :
    ‖phi σ w‖ ≤ ‖w⁻¹ ^ 2‖ * c ^ (-2 * σ.re) := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc (hcw.trans (Complex.abs_im_le_norm w))
  unfold phi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hc (hcw.trans (Complex.abs_im_le_norm w)) (by linarith)
end GlobalTheory.HeckeTwo
