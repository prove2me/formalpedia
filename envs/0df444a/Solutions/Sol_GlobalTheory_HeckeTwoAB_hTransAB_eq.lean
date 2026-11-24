-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.hTransAB_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:30.130985+00:00
-- url     : https://prove2.me/submissions/34f4f279-e001-476c-9864-cb2ca0d684b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_norm_wt

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
theorem _root_.solution (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) :
    (fun σ => hTransAB a b σ ν y) = fun σ => ∫ t, F a b ν y σ t := by
  funext σ
  unfold hTransAB F
  congr 1; funext t
  congr 2
  rw [show (t : ℂ) + (y : ℂ) * I = wt y t from rfl, norm_wt hy,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
end GlobalTheory.HeckeTwoAB
