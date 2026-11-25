-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.hasTemperateGrowth_infinitePoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:11.062666+00:00
-- url     : https://prove2.me/submissions/4fe05450-f059-4654-9670-37935c2a40cf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
import Theorems.Thm_GroundTheory_Global_hasTemperateGrowth_finsetProd
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.HeckeCharacter
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution : χ.infinitePoly.HasTemperateGrowth := by
  have h1 : ∀ w : {w // IsReal w}, (fun x : mixedSpace K ↦
      ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs).HasTemperateGrowth := fun w ↦ by
    have h := (((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
    exact h
  have h2 : ∀ w : {w // IsComplex w}, (fun x : mixedSpace K ↦
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^
        (χ.infiniteWeight w).natAbs).HasTemperateGrowth := by
    intro w
    by_cases hw : 0 < χ.infiniteWeight w
    · simp only [if_pos hw]
      have h := (((Complex.conjCLE.toContinuousLinearMap.comp ((ContinuousLinearMap.proj w :
        ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ))) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
    · simp only [if_neg hw]
      have h := ((((ContinuousLinearMap.proj w : ({w // IsComplex w} → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.snd ℝ ({w // IsReal w} → ℝ)
          ({w // IsComplex w} → ℂ)) : mixedSpace K →L[ℝ] ℂ)).hasTemperateGrowth).pow (χ.infiniteWeight w).natAbs
      exact h
  exact (hasTemperateGrowth_finsetProd _ fun w _ ↦ h1 w).mul
    (hasTemperateGrowth_finsetProd _ fun w _ ↦ h2 w)
end GroundTheory.Global.HeckeCharacter
