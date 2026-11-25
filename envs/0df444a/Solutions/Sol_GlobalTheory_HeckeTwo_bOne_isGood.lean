-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.bOne_isGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:41.278927+00:00
-- url     : https://prove2.me/submissions/6af48e5d-99c9-4485-bcc5-bd567b23200f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeFourierTermWirtingerWordDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoTermIteratedFDerivSummableBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinNonconstantFourierSumSmoothHolomorphic
import Theorems.Thm_GlobalTheory_T_contDiffOn_heckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_T_heckeFourierTerm_wirtingerWord_differentiableOn
import Theorems.Thm_GlobalTheory_T_heckeWeightTwo_isGood_of_tsum
import Theorems.Thm_GlobalTheory_T_heckeWeightTwo_term_iteratedFDeriv_summable_bound


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
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  intro F _ _ _ 𝔞 𝔟
  refine GlobalTheory.T.heckeWeightTwo_isGood_of_tsum F _ (fun p σ z => fTerm σ z (p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ×
      NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1.out.1 p.2.1) _
    (fun p σ hσ => GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm F _ _ p.1.out.2.2 σ hσ) (fun p w z hz => GlobalTheory.T.heckeFourierTerm_wirtingerWord_differentiableOn F _ _ p.1.out.2.2 w z hz)
    (GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟) ?_
  intro σ hσ z hz
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟 {σ} isCompact_singleton (by simpa using hσ) {z} isCompact_singleton
    (by simpa using hz) 0
  have hs : Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
      fTerm σ z p.1.out.1 p.2.1) := by
    refine Summable.of_norm_bounded hu fun p => ?_
    have := hb p σ rfl z rfl
    rwa [norm_iteratedFDeriv_zero] at this
  unfold bOne
  exact (hs.tsum_prod' fun c => hs.prod_factor c).symm
end GlobalTheory.HeckeTwo
