-- Prove2me | solution 1 for GlobalTheory.T.tsum_latticePair_unitQuotient_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:43.899724+00:00
-- url     : https://prove2.me/submissions/bfb52cfd-1499-497f-825a-1a136bad406c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroupStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_tsum_latRel_regroup


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  first | exact @GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup | exact GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup | (intros; apply GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup <;> assumption)
end _root_.GlobalTheory.T
