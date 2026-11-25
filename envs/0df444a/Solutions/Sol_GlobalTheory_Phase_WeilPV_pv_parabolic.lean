-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.pv_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:02.065282+00:00
-- url     : https://prove2.me/submissions/0ec04393-c2da-4206-9450-3ac9dab781fc

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
import Theorems.Thm_GlobalTheory_Phase_WeilPV_vac_trans
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_sb
import Theorems.Thm_GlobalTheory_Phase_IsMu_mul
import Theorems.Thm_GlobalTheory_Phase_Ph_mul
import Theorems.Thm_GlobalTheory_T_siegelParabolic_transform_values_rootOfUnity


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
theorem _root_.solution (he : Even (Fintype.card κ)) {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (h0 : σ.toBlocks₂₁ = 0)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans hσ hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity κ ι he σ hσ h0 φ ψ (pv_sb h) hψ t y
  rw [e]; exact hu.mul (h.2 _)
end GlobalTheory.Phase.WeilPV
