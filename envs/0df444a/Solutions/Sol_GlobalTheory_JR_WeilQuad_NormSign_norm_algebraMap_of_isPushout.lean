-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NormSign.norm_algebraMap_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:13.346697+00:00
-- url     : https://prove2.me/submissions/ff1f6149-0ce8-4cc9-9dc5-a45b23291e8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_norm_one_tmul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NormSign
namespace GlobalTheory.JR.WeilQuad.NormSign
theorem _root_.solution : ∀ (F E K L : Type) [Field F] [Field E] [Field K] [CommRing L] [Algebra F E] [Algebra F K] [Algebra F L]
    [Algebra K L] [Algebra E L] [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F E],
    Algebra.IsPushout F E K L → ∀ z : E, Algebra.norm K (algebraMap E L z) = algebraMap F K (Algebra.norm F z) := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ h z
  haveI := h.symm
  have he : Algebra.IsPushout.equiv F K E L ((1 : K) ⊗ₜ[F] z) = algebraMap E L z := by
    simp [Algebra.IsPushout.equiv_tmul]
  rw [← he, Algebra.norm_eq_of_algEquiv, norm_one_tmul]
end GlobalTheory.JR.WeilQuad.NormSign
