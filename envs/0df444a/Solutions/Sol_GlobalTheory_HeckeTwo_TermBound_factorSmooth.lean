-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermBound.factorSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:47.886826+00:00
-- url     : https://prove2.me/submissions/3acb70cf-3d77-4996-bd62-f0f9ae0d09c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactPiUpperHalfPlaneImBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivProdCoordLeLeibnizStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformReprStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermIntegralPolynomialDecayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiFourierTransformBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivHeckeFourierFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FTermIteratedFDerivBound
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_contDiffOn_hTrans


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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermBound
namespace GlobalTheory.HeckeTwo.TermBound
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν β : ℝ) (hβ : β ≠ 0) :
    ContDiffOn ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
      hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => ((ν * β * w.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Complex.reCLM.contDiff)
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hre)
  have h2 : ContDiffOn ℝ ∞ (fun w : ℂ => hTrans σ ν (β * w.im)) {w : ℂ | 0 < w.im} := by
    refine (GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans σ hσ ν).comp
      (contDiff_const.mul Complex.imCLM.contDiff : ContDiff ℝ ∞ fun w : ℂ => β * w.im).contDiffOn ?_
    intro w hw; exact mul_ne_zero hβ (ne_of_gt hw)
  exact h1.contDiffOn.mul h2
end GlobalTheory.HeckeTwo.TermBound
