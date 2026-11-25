-- Prove2me | solution 1 for GlobalTheory.T.upperHalfPlaneProduct_prod_im_rpow_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:50.834683+00:00
-- url     : https://prove2.me/submissions/5283d903-afe2-4e6c-a089-084ecd7dfbfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOnStatement
import Theorems.Thm_GlobalTheory_upperHalf_prodImPow_contDiffOn


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), ContDiffOn ℝ ∞ (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  first | exact @GlobalTheory.upperHalf_prodImPow_contDiffOn | exact GlobalTheory.upperHalf_prodImPow_contDiffOn | (intros; apply GlobalTheory.upperHalf_prodImPow_contDiffOn <;> assumption)
end _root_.GlobalTheory.T
