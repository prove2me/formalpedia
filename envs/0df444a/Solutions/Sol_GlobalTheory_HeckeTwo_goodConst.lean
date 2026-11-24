-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.goodConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:36.100504+00:00
-- url     : https://prove2.me/submissions/7a544cd5-e149-40fd-9e32-93017c825541

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
import Theorems.Thm_GlobalTheory_HeckeTwo_isGood_const

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
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) :=
  fun F _ _ a ha => isGood_const F a ha
end GlobalTheory.HeckeTwo
