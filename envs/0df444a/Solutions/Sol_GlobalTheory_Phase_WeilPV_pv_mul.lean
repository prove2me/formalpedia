-- Prove2me | solution 1 for GlobalTheory.Phase.WeilPV.pv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:57.340973+00:00
-- url     : https://prove2.me/submissions/8024b232-6703-47ec-882b-b12ae333a7b4

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
import Theorems.Thm_GlobalTheory_Phase_WeilPV_trans_unique
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_sb
import Theorems.Thm_GlobalTheory_Phase_ParabValues_trans_unique
import Theorems.Thm_GlobalTheory_SW_exists_weil_of_symplectic
import Theorems.Thm_GlobalTheory_SW_transS_comp


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
theorem _root_.solution (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by
  intro φ ψ hψ t h
  obtain ⟨w, hw⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ he hσ
  obtain ⟨w', hw'⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ' he hσ'
  obtain ⟨s1, t1, -⟩ := hw φ (pv_sb h)
  obtain ⟨s2, t2, -⟩ := hw' (w φ) s1
  have t3 := GlobalTheory.SW.transS_comp κ ι σ σ' hσ hσ' _ _ _ t1 t2
  rw [trans_unique (mul_mem hσ' hσ) hψ s2 t t3]
  exact H' _ _ s2 t2 (H _ _ s1 t1 h)
end GlobalTheory.Phase.WeilPV
