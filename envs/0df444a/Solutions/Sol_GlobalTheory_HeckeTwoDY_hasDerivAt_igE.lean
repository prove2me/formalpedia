-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.hasDerivAt_igE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:41:53.492512+00:00
-- url     : https://prove2.me/submissions/22b8954b-e7d9-403c-bce0-0363ead7655e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_wt_ne
import Theorems.Thm_GlobalTheory_HeckeTwoDY_conj_wt_ne
import Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_wt
import Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_cwt
import Theorems.Thm_GlobalTheory_HeckeTwoDY_hasDerivAt_invpow
import Theorems.Thm_GlobalTheory_HeckeTwoDY_two_y_div

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
theorem _root_.solution (a b : ℕ) (σ : ℂ) (ν t : ℝ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y' => igE a b σ ν y' t)
      (I * (-(a : ℂ) - σ) * igE (a + 1) b σ ν y t + I * ((b : ℂ) + σ) * igE a (b + 1) σ ν y t) y := by
  have hA := hasDerivAt_invpow (hasDerivAt_wt t y) (wt_ne hy) a
  have hB := hasDerivAt_invpow (hasDerivAt_cwt t y) (conj_wt_ne hy) b
  have hq : HasDerivAt (fun y' : ℝ => t ^ 2 + y' ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (t ^ 2)
  have hL := (((hq.log (q_pos hy).ne').ofReal_comp).mul_const (-σ)).cexp
  have h := ((hA.mul hB).mul hL).mul_const (Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))))
  unfold igE
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [two_y_div hy]
  ring
end GlobalTheory.HeckeTwoDY
