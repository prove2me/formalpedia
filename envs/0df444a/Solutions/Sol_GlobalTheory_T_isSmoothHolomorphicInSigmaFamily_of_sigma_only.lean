-- Prove2me | solution 1 for GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_of_sigma_only
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:09.454893+00:00
-- url     : https://prove2.me/submissions/a9b97db9-16dd-4012-8363-507e276a3a85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnlyStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_goodConst


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  first | exact @GlobalTheory.HeckeTwo.goodConst | exact GlobalTheory.HeckeTwo.goodConst | (intros; apply GlobalTheory.HeckeTwo.goodConst <;> assumption)
end _root_.GlobalTheory.T
