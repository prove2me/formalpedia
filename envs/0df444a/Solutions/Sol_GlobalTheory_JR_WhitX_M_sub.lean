-- Prove2me | solution 1 for GlobalTheory.JR.WhitX.M_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:12.230799+00:00
-- url     : https://prove2.me/submissions/5f838070-d5ae-4663-bc93-c1379e76876f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralPsiKOverScaledIntegersEqVolumeIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersKStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleExistsSqRootNearOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsOneEtaleAlgebraMulInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedSetEmptyOutsideNormCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianPairNormPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScalingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventually
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WhitX
namespace GlobalTheory.JR.WhitX
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (c : F) (hc : c ≠ 0) :
    ∃ M : AddSubgroup A.K, (M : Set A.K) = {z : A.K | c • z ∈ A.OK} ∧ IsOpen (M : Set A.K) ∧ IsCompact (M : Set A.K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  refine ⟨(R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c), ?_, ?_, ?_⟩
  · ext z; simp [← hR]
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c • z) ⁻¹' A.OK := by
      ext z; simp [← hR]
    rw [this]; exact hOo.preimage (continuous_const_smul c)
  · have : ((R.toAddSubgroup).comap (DistribMulAction.toAddMonoidHom A.K c) : Set A.K) = (fun z => c⁻¹ • z) '' A.OK := by
      ext z; simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, DistribMulAction.toAddMonoidHom_apply]
      constructor
      · intro h; exact ⟨c • z, by simpa [← hR] using h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_smul, mul_inv_cancel₀ hc, ← hR] using hw
    rw [this]; exact hOc.image (continuous_const_smul c⁻¹)
end GlobalTheory.JR.WhitX
