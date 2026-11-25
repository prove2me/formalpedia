-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.pv_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:33.77828+00:00
-- url     : https://prove2.me/submissions/8abb7e2f-7589-4c91-9b24-5c608d58aa1c

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
import Theorems.Thm_GlobalTheory_Phase_VacShape_vacuum_shape
import Theorems.Thm_GlobalTheory_Phase_shape_conj_chr_mul
import Theorems.Thm_GlobalTheory_Phase_val_trans_J
import Theorems.Thm_GlobalTheory_T_schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase


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
theorem _root_.solution (he : Even (Fintype.card κ))
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS (Matrix.J ι ℚ) φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans (SymplecticGroup.J_mem ι ℚ) hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.Phase.val_trans_J κ ι he φ ψ (pv_sb h) hψ t y
  rw [e]
  exact hu.mul (GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase κ ι _
    ((GlobalTheory.Phase.shape_conj_chr_mul κ ι φ ((GlobalTheory.Phase.VacShape.vacuum_shape κ ι φ).2.1 h)).2.1 y'))
end GlobalTheory.Phase.WeilPV
