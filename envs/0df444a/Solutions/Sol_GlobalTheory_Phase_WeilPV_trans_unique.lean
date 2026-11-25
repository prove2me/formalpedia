-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.trans_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:39.7928+00:00
-- url     : https://prove2.me/submissions/faaff247-85f7-4164-9282-d538aed2862f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationLawMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSIntertwines
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TransSUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RootOfUnityPhaseVacuumSiegelThetaTransform
import Theorems.Thm_GlobalTheory_SW_I_mem_siegel
import Theorems.Thm_GlobalTheory_SW_eq_of_thS_eq
import Theorems.Thm_GlobalTheory_SiegelAction_symplectic_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.WeilPV
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Phase.WeilPV
theorem _root_.solution {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (h1 : IsSB ψ) (h2 : IsSB ψ') (t1 : TransS σ φ ψ)
    (t2 : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' h1 h2 _ hs fun ζ => ?_
  have e1 := t1 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e2 := t2 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e := e1.trans e2.symm
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
    Matrix.vecMul_one] at e
  exact e
end GlobalTheory.Phase.WeilPV
