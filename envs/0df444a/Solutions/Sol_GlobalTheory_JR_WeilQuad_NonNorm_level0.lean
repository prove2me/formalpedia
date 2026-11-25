-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NonNorm.level0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:39.19542+00:00
-- url     : https://prove2.me/submissions/f33b0d36-f00d-4139-ac34-19155c4e9bec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HaarMeasureLUnitSmulAbsKSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticGaussIntegralStableOfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussAtUniformiser
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NonNorm_kerL_one
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_T_quadraticGaussIntegral_stable_of_dual_lattice
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
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
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
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NonNorm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.NonNorm
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ O : Subring A.L, IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = (O : Set A.L) → IsStableGauss A ψ x μ t (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ A ψ x μ hψ hμ O hOo hOc hOs htr t hD
  obtain ⟨-, -, hN, htrL, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have h1 : (1 : A.L) ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} := by rw [hD]; exact O.one_mem
  have hM : ∀ m ∈ O, A.psiK ψ (t * x * A.NL m) = 1 := fun m hm => by
    obtain ⟨z, hz, hzs⟩ := htr (A.NL m) (by rw [hN]; exact O.mul_mem hm (hOs m hm))
    have := h1 z hz
    rwa [kerL_one, hzs] at this
  have hDeq : ((O.toAddSubgroup : AddSubgroup A.L) : Set A.L) =
      {y : A.L | ∀ m ∈ O.toAddSubgroup, A.kerL ψ (t * x) y m = 1} := by
    simpa using hD.symm
  have hG := GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice F E A ψ x μ hψ hμ t O.toAddSubgroup O.toAddSubgroup hOo hOc hOo hOc
    (fun m hm => hM m hm) hDeq
  convert hG using 1
  simp only [gaussInt, Subring.coe_toAddSubgroup]
  rw [setIntegral_congr_fun hOo.measurableSet (g := fun _ => (1 : ℂ)) (fun y hy => hM y hy)]
  simp [Measure.real]
end GlobalTheory.JR.WeilQuad.NonNorm
