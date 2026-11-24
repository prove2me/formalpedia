-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.norm_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:43:38.299855+00:00
-- url     : https://prove2.me/submissions/5d2b5be6-c72f-4b2c-ae83-e6a90321b408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_wt_eq
import Theorems.Thm_GlobalTheory_HeckeTwoC_norm_tI_eq


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
open GlobalTheory GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC
namespace GlobalTheory.HeckeTwoAB
theorem _root_.solution {y : ℝ} (hy : y ≠ 0) (t : ℝ) : ‖wt y t‖ = Real.exp (L y t) := by
  rw [wt_eq hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, L, Real.exp_add,
    Real.exp_log (abs_pos.2 hy), ← norm_tI_eq]
end GlobalTheory.HeckeTwoAB
