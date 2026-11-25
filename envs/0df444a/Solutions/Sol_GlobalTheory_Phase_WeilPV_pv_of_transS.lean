-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.pv_of_transS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:03.189477+00:00
-- url     : https://prove2.me/submissions/2a5a2500-5564-450d-9e70-ceeb5f66554e

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
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_parabolic
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_J
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_mul
import Theorems.Thm_GlobalTheory_SW_symplectic_eq_parabolic_J_parabolic_J_parabolic


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
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  intro κ ι _ _ _ he σ hσ
  obtain ⟨p₁, h1, p₂, h2, p₃, h3, z1, z2, z3, rfl⟩ :=
    GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ := SymplecticGroup.J_mem ι ℚ
  have P : ∀ p ∈ Matrix.symplecticGroup ι ℚ, p.toBlocks₂₁ = 0 →
      ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS p φ ψ → PV φ → PV ψ :=
    fun p hp z φ ψ hψ t h => pv_parabolic he hp z hψ t h
  have Q : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (Matrix.J ι ℚ) φ ψ → PV φ → PV ψ :=
    fun φ ψ hψ t h => pv_J he hψ t h
  have a := mul_mem h1 hJ
  have b := mul_mem a h2
  have c := mul_mem b hJ
  exact pv_mul he h3 c (P _ h3 z3) (pv_mul he hJ b Q (pv_mul he h2 a (P _ h2 z2)
    (pv_mul he hJ h1 Q (P _ h1 z1))))
end GlobalTheory.Phase.WeilPV
