-- Prove2me | solution 1 for GlobalTheory.HeckeTwoDY.continuous_igE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:53.49337+00:00
-- url     : https://prove2.me/submissions/4db7ba59-05bb-4e16-a574-6fd6334bf532

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
import Theorems.Thm_GlobalTheory_HeckeTwoDY_q_pos
import Theorems.Thm_GlobalTheory_HeckeTwoDY_wt_ne
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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory
namespace GlobalTheory.HeckeTwoDY
theorem _root_.solution (a b : ℕ) (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : Continuous (fun t => igE a b σ ν y t) := by
  unfold igE
  have hw : Continuous fun t : ℝ => wt t y := by unfold wt; fun_prop
  have h1 : Continuous fun t : ℝ => (wt t y)⁻¹ := hw.inv₀ (fun t => wt_ne hy)
  have h2 : Continuous fun t : ℝ => ((starRingEnd ℂ) (wt t y))⁻¹ :=
    (Complex.continuous_conj.comp hw).inv₀ (fun t => conj_wt_ne hy)
  have h3 : Continuous fun t : ℝ => Real.log (t ^ 2 + y ^ 2) :=
    (by fun_prop : Continuous fun t : ℝ => t ^ 2 + y ^ 2).log (fun t => (q_pos hy).ne')
  exact (((h1.pow a).mul (h2.pow b)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp h3).mul continuous_const))).mul (by fun_prop)
end GlobalTheory.HeckeTwoDY
