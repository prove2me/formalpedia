-- Prove2me | solution 1 for GlobalTheory.HeckeTwoC.bound_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:13.874054+00:00
-- url     : https://prove2.me/submissions/d9a4a1e1-686d-490e-ad66-6b5dbe6ae0f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_lg_nonneg
import Theorems.Thm_GlobalTheory_HeckeTwoC_norm_G

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
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory
namespace GlobalTheory.HeckeTwoC
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G σ t‖ ≤ Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G]
  apply Real.exp_le_exp.2
  have := lg_nonneg t
  nlinarith
end GlobalTheory.HeckeTwoC
