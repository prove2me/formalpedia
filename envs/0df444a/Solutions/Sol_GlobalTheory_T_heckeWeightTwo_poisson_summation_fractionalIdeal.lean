-- Prove2me | solution 1 for GlobalTheory.T.heckeWeightTwo_poisson_summation_fractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:33.371466+00:00
-- url     : https://prove2.me/submissions/34da7136-6501-42e9-9f48-d61f4a93a293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoPoissonSummationFractionalIdealStatement
import Theorems.Thm_GlobalTheory_HeckeTwoPoisson_poisson


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧ HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  first | exact @GlobalTheory.HeckeTwoPoisson.poisson | exact GlobalTheory.HeckeTwoPoisson.poisson | (intros; apply GlobalTheory.HeckeTwoPoisson.poisson <;> assumption)
end _root_.GlobalTheory.T
