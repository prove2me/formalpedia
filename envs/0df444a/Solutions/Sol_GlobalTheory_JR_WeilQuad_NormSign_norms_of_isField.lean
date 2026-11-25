-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NormSign.norms_of_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:57.766732+00:00
-- url     : https://prove2.me/submissions/67da87a7-514b-4430-a453-ce366c0ef6b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_exists_valuativeRel_of_normed
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_norm_algebraMap_of_isPushout
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NormSign_mul_norm_of_not_norm
import Theorems.Thm_GlobalTheory_T_exists_norm_eq_neg_one_of_unramified_values
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_finrank_eq
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
import Theorems.Thm_GroundTheory_LocalField_exists_isNonarchimedeanLocalField_valuativeExtension
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
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    A.NL 0 = 0 ∧
    (∀ s t : A.Kˣ, (¬ ∃ y, A.NL y = s) → (¬ ∃ y, A.NL y = t) → ∃ y, A.NL y = ((s * t : A.Kˣ) : A.K)) ∧
      ∃ y, A.NL y = ((-1 : A.Kˣ) : A.K) := by
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := hU.ultraF
  haveI := hU.ultraE
  haveI := hU.lcF
  haveI := hU.lcE
  haveI := hU.charZero
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      hU.finrank_eq]
  haveI : CharZero A.K := charZero_of_injective_algebraMap (algebraMap F A.K).injective
  obtain ⟨vF, hFloc, hFv⟩ := exists_valuativeRel_of_normed F
  refine ⟨?_, ?_⟩
  · haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
    exact Algebra.norm_zero (R := A.K) (S := A.L)
  constructor
  · intro s t hs ht
    obtain ⟨vK, tK, hKloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension F A.K
    exact @mul_norm_of_not_norm A.K A.L _ vK tK hKloc _ _ _ hKL s t hs ht
  · obtain ⟨vE, hEloc, hEv⟩ := exists_valuativeRel_of_normed E
    haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
    obtain ⟨z, hz⟩ := GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values F E (fun y => by
      obtain ⟨x, hx⟩ := hU.unram y
      exact ⟨x, by rw [hEv, norm_algebraMap', hx], by rw [hEv, norm_algebraMap', hx]⟩)
    refine ⟨algebraMap E A.L z, ?_⟩
    have := norm_algebraMap_of_isPushout F E A.K A.L A.push z
    simp only [Et.NL, this, hz, map_neg, map_one, Units.val_neg, Units.val_one]
end GlobalTheory.JR.WeilQuad.NormSign
