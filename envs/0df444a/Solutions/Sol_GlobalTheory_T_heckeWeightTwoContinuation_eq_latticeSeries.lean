-- Prove2me | solution 1 for GlobalTheory.T.heckeWeightTwoContinuation_eq_latticeSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:25.228172+00:00
-- url     : https://prove2.me/submissions/bfbc9eaf-e1df-4010-8f33-aaba454d3161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationEqLatticeSeries
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationEqLatticeSeriesStatement
import Theorems.Thm_GlobalTheory_HeckeTwoEq_gFun_eq_eisSum


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ σ : ℂ, 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) ∧ GlobalTheory.HeckeTwo.gFun Zb 𝔞 𝔟 σ z = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisSum 𝔞 𝔟 2 σ z := by
  first | exact @GlobalTheory.HeckeTwoEq.gFun_eq_eisSum | exact GlobalTheory.HeckeTwoEq.gFun_eq_eisSum | (intros; apply GlobalTheory.HeckeTwoEq.gFun_eq_eisSum <;> assumption)
end _root_.GlobalTheory.T
