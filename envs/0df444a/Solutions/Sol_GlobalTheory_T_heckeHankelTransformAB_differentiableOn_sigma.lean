-- Prove2me | solution 1 for GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:39:30.274389+00:00
-- url     : https://prove2.me/submissions/ae79a5ad-516e-4068-9427-427bd68c5dc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigmaStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_hTransAB_differentiableOn


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
end _root_.GlobalTheory.T
