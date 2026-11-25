-- Prove2me | solution 1 for GlobalTheory.T.heckeEisensteinZeroFrequencyPart_isSmoothHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:47.008834+00:00
-- url     : https://prove2.me/submissions/3e47db1a-1173-4a5f-84c8-bfe47435232f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorpStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_bZero_isGood


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb R : ℂ → ℂ), Differentiable ℂ R → (∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) → GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bZero Zb 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bZero_isGood | exact GlobalTheory.HeckeTwo.bZero_isGood | (intros; apply GlobalTheory.HeckeTwo.bZero_isGood <;> assumption)
end _root_.GlobalTheory.T
