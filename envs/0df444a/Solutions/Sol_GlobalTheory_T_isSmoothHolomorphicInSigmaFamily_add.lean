-- Prove2me | solution 1 for GlobalTheory.T.isSmoothHolomorphicInSigmaFamily_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:07.893406+00:00
-- url     : https://prove2.me/submissions/63b10280-5fcb-461b-b63f-902225f898c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAddStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_isGood_add


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (P Q : ℂ → (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) → ℂ), GlobalTheory.HeckeTwo.IsGood P → GlobalTheory.HeckeTwo.IsGood Q → GlobalTheory.HeckeTwo.IsGood (fun σ z => P σ z + Q σ z) := by
  first | exact @GlobalTheory.HeckeTwo.isGood_add | exact GlobalTheory.HeckeTwo.isGood_add | (intros; apply GlobalTheory.HeckeTwo.isGood_add <;> assumption)
end _root_.GlobalTheory.T
