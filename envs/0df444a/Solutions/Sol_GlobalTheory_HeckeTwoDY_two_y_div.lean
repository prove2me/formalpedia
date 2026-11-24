-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.two_y_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:58.01506+00:00
-- url     : https://prove2.me/submissions/158f936f-f2d8-4b0b-bfa9-7afd03309857

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_wt_ne
import Theorems.Thm_GlobalTheory_HeckeTwoDY_conj_wt
import Theorems.Thm_GlobalTheory_HeckeTwoDY_conj_wt_ne

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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution {t y : ℝ} (hy : y ≠ 0) :
    (((2 * y / (t ^ 2 + y ^ 2) : ℝ)) : ℂ) = I * ((wt t y)⁻¹ - ((starRingEnd ℂ) (wt t y))⁻¹) := by
  have hq := q_pos (t := t) hy
  have hw := wt_ne (t := t) hy
  have hc := conj_wt_ne (t := t) hy
  have hprod : wt t y * (starRingEnd ℂ) (wt t y) = ((t ^ 2 + y ^ 2 : ℝ) : ℂ) := by
    rw [conj_wt]; unfold wt; push_cast; ring_nf; rw [I_sq]; ring
  have hq' : ((t ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [inv_sub_inv hw hc, hprod, conj_wt]
  unfold wt
  push_cast
  field_simp
  ring_nf; rw [I_sq]; ring
end GlobalTheory.HeckeTwoDY
