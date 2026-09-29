-- Prove2me | solution 1 for NumberField.LevelArith.exists_inhomogeneousCochains_d_two_three_eq_sIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ecbfe8aa-230f-51ca-a15b-1dbbf6f8fcfc

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Theorems.Thm_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
import Theorems.Thm_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele.NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele.NumberField.LevelArith"
p2m_open_scoped "NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele.NumberField.LevelArith NumberField.PlaceDecomp"
open scoped NumberField.InfPlaceDecomp

namespace NumberField
p2m_export "NumberField" "place InfinitePlace PlaceAbove.above SIdele.obj FiniteSIdele.localUnits InfPlaceDecomp.decomp InfPlaceDecomp.localUnits ArchIdele.above SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one PlaceDecomp.exists_inhomogeneousCochains_d_two_three_eq_adicCompletion LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField placesOverPrimesFinset ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset"
namespace H3Vanish
p2m_open "NumberField.LevelArith NumberField"

section Exactness

variable {G : Type} [Group G] (A : Rep ℤ G)

theorem isZero_groupCohomology_three_of_forall
    (h : ∀ u : (Fin 3 → G) → A, ((inhomogeneousCochains A).d 3 4).hom u = 0 →
      ∃ c : (Fin 2 → G) → A, ((inhomogeneousCochains A).d 2 3).hom c = u) :
    Limits.IsZero (groupCohomology A 3) := by
  rw [groupCohomology, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (inhomogeneousCochains A) 2 3 4 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  exact h x₂ hx₂

theorem forall_exists_of_isZero_groupCohomology_three (hZ : Limits.IsZero (groupCohomology A 3))
    (u : (Fin 3 → G) → A) (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → G) → A, ((inhomogeneousCochains A).d 2 3).hom c = u := by
  rw [groupCohomology, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (inhomogeneousCochains A) 2 3 4 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hZ
  exact hZ u hu

theorem eq_zero_of_isZero {M : ModuleCat ℤ} (hZ : Limits.IsZero M) (x : M) : x = 0 := by
  have h := hZ.eq_of_src (𝟙 M) 0
  have h2 := congrArg (fun f => (ModuleCat.Hom.hom f) x) h
  simpa using h2

end Exactness

end NumberField.LevelArith.H3Vanish

open NumberField.LevelArith.H3Vanish in

theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (hinf : ∀ (v : InfinitePlace ↥(levelField L F hLF)) (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))), g ∈ NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) v → g = 1)
    (u : (Fin 3 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)))
    (hu : ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) → (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)), ((inhomogeneousCochains (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))).d 2 3).hom c = u := by

  have hunr : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S → (w.under (𝓞 ↥L)).asIdeal.ramificationIdx' w.asIdeal = 1 := fun w hw =>
    NumberField.LevelArith.ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset S L F hLF hF w hw

  have hfinZ : ∀ v : HeightOneSpectrum (𝓞 ↥L),
      Limits.IsZero (groupCohomology (NumberField.FiniteSIdele.localUnits ↥L ↥(levelField L F hLF) v) 3) := fun v =>
    isZero_groupCohomology_three_of_forall _
      (NumberField.PlaceDecomp.exists_inhomogeneousCochains_d_two_three_eq_adicCompletion ↥L ↥(levelField L F hLF)
        (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v))
  have hinfZ : ∀ v : InfinitePlace ↥L,
      Limits.IsZero (groupCohomology (NumberField.InfPlaceDecomp.localUnits ↥L ↥(levelField L F hLF)
        (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)) 3) := by
    intro v
    haveI : Subsingleton ↥(NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.ArchIdele.above ↥L ↥(levelField L F hLF) v)) :=
      ⟨fun a b => Subtype.ext ((hinf _ a.1 a.2).trans (hinf _ b.1 b.2).symm)⟩
    exact isZero_groupCohomology_succ_of_subsingleton _ 2

  have hbij := NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
    ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) hunr 2
  have hall : ∀ x : groupCohomology (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) 3, x = 0 := by
    intro x
    apply hbij.1
    refine Prod.ext ?_ ?_
    · funext v
      exact (eq_zero_of_isZero (hfinZ v.1) _).trans (eq_zero_of_isZero (hfinZ v.1) _).symm
    · funext v
      exact (eq_zero_of_isZero (hinfZ v) _).trans (eq_zero_of_isZero (hinfZ v) _).symm
  haveI : Subsingleton ↥(groupCohomology (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) 3) :=
    ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact forall_exists_of_isZero_groupCohomology_three _ (ModuleCat.isZero_of_subsingleton _) u hu

end S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele
end P2MW
export P2MW.S_NumberField_LevelArith_exists_inhomogeneousCochains_d_two_three_eq_sIdele (solution)
