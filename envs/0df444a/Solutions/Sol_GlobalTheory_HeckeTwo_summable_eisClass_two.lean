-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.summable_eisClass_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:05:20.53285+00:00
-- url     : https://prove2.me/submissions/70dc5ab7-2831-48d0-b9a1-46efa4c2f703

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPairStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableGaussianExtensionNormRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeSummandWeightTwoBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinLatticeClassWeightTwo
import Theorems.Thm_GlobalTheory_T_algebraNorm_rat_gaussianExtensionOfPair
import Theorems.Thm_GlobalTheory_T_finite_gaussianExtension_units_quot_units
import Theorems.Thm_GlobalTheory_T_hilbertEisensteinLatticeSummand_weightTwo_bound
import Theorems.Thm_GlobalTheory_T_summable_gaussianExtension_norm_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end GlobalTheory.HeckeTwo
