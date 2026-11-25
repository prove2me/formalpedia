-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:38.976432+00:00
-- url     : https://prove2.me/submissions/c03bee8b-6d40-4473-89bb-fa4f8274e5c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinWeightTwoQExpansion
import Theorems.Thm_GlobalTheory_HeckeTwoExp_bOne_zero_expansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 =
      ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c :=
  fun _ _ _ _ 𝔞 𝔟 z hz => bOne_zero_expansion 𝔞 𝔟 z hz
end GlobalTheory.HeckeTwoExp
