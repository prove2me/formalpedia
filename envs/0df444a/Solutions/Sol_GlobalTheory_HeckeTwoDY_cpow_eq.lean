-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.cpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:48.662801+00:00
-- url     : https://prove2.me/submissions/1ec19cc8-84eb-4d78-aa43-cb5ddbec3035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_wt_ne
import Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_wt

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
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {t y : ℝ} (hy : y ≠ 0) (σ : ℂ) :
    ((‖wt t y‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp ((Real.log (t ^ 2 + y ^ 2) : ℂ) * (-σ)) := by
  have hq := q_pos (t := t) hy
  have hn : (0 : ℝ) < ‖wt t y‖ := norm_pos_iff.2 (wt_ne hy)
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_log hn.le]
  congr 1
  have : Real.log (t ^ 2 + y ^ 2) = 2 * Real.log ‖wt t y‖ := by
    rw [norm_wt, Real.log_sqrt hq.le]; ring
  rw [this]; push_cast; ring
end GlobalTheory.HeckeTwoDY
