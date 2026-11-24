-- Prove2me | solution 1 for GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:08.672577+00:00
-- url     : https://prove2.me/submissions/60fb1180-0893-434b-a4a4-315ba56b7154

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeftStatement
import Theorems.Thm_GlobalTheory_HeckeTwoMul_isGood_mul


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (k : ℂ → ℂ) (P : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), DifferentiableOn ℂ k GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood (fun σ z => k σ * P σ z) := by
  first | exact @GlobalTheory.HeckeTwoMul.isGood_mul | exact GlobalTheory.HeckeTwoMul.isGood_mul | (intros; apply GlobalTheory.HeckeTwoMul.isGood_mul <;> assumption)
end _root_.GlobalTheory.T
