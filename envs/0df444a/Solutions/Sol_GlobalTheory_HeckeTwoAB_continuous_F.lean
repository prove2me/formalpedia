-- Prove2me | solution 1 for GlobalTheory.HeckeTwoAB.continuous_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:41:48.061029+00:00
-- url     : https://prove2.me/submissions/f7301cd4-2dde-4250-9fac-4ae3d6bb7bfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Theorems.Thm_GlobalTheory_HeckeTwoAB_wt_ne
import Theorems.Thm_GlobalTheory_HeckeTwoAB_continuous_L

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
theorem _root_.solution (a b : ℕ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) (σ : ℂ) : Continuous (F a b ν y σ) := by
  unfold F
  have hw : Continuous (wt y) := by unfold wt; fun_prop
  have h1 : Continuous fun t => (wt y t)⁻¹ := hw.inv₀ (wt_ne hy)
  have h2 : Continuous fun t => ((starRingEnd ℂ) (wt y t))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => (map_ne_zero _).2 (wt_ne hy t))
  have h3 : Continuous fun t => Complex.exp ((L y t : ℂ) * (-2 * σ)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_L).mul continuous_const)
  have h4 : Continuous fun t : ℝ => Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) := by fun_prop
  exact (((h1.pow a).mul (h2.pow b)).mul h3).mul h4
end GlobalTheory.HeckeTwoAB
