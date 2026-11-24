-- Prove2me | solution 1 for GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:35.001903+00:00
-- url     : https://prove2.me/submissions/e1d11196-09f4-471d-87a0-bbed7b8f9a0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoTermIteratedFDerivSummableBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoTermIteratedFDerivSummableBoundStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_fTerm_deriv_summable_bound


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | exact GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | (intros; apply GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound <;> assumption)
end _root_.GlobalTheory.T
