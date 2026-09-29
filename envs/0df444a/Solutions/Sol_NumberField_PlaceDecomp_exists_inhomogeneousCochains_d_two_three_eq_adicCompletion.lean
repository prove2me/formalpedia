-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c177e5d2-386d-576a-ae84-cd674b78eb09

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_Rep_nonempty_tateCohomology_trivial_iso_of_h1_h2
import Theorems.Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.coe_tateδneg2_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun"
p2m_attr_erase "simp" "SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField IsDedekindDomain M4aHerbrand"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField.PlaceDecomp"
namespace NumberField
p2m_export "NumberField" "place PlaceDecomp.decomp PlaceDecomp.exists_fundamentalClass_units_adicCompletion"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp exists_fundamentalClass_units_adicCompletion"
namespace H3
p2m_open "NumberField.PlaceDecomp NumberField"
universe u

theorem exists_d_two_three_eq_of_isZero {G : Type} [Group G] (A : Rep ℤ G)
    (hZ : Limits.IsZero (groupCohomology A 3))
    (u : (Fin 3 → G) → A) (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → G) → A, ((inhomogeneousCochains A).d 2 3).hom c = u := by
  have hex : (inhomogeneousCochains A).ExactAt 3 :=
    ((inhomogeneousCochains A).exactAt_iff_isZero_homology 3).2 hZ
  rw [(inhomogeneousCochains A).exactAt_iff' 2 3 4 (by simp) (by simp)] at hex
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex u hu
  exact ⟨c, hc⟩

theorem addMonoidHom_int_eq_zero {X : Type} [AddGroup X] [Finite X] (f : X →+ ℤ) : f = 0 := by
  ext x
  have h1 : Nat.card X • x = 0 := card_nsmul_eq_zero'
  have h2 : f (Nat.card X • x) = 0 := by rw [h1, map_zero]
  rw [map_nsmul, nsmul_eq_mul, mul_eq_zero] at h2
  rcases h2 with h | h
  · exact absurd (Nat.cast_eq_zero.1 h) (Nat.card_pos (α := X)).ne'
  · exact h

scoped instance isTrivial_res_trivial {G H : Type} [Group G] [Group H] (f : H →* G) :
    (Rep.res f (Rep.trivial ℤ G ℤ)).IsTrivial where
  out _ := rfl

theorem isZero_H1_trivial {G H : Type} [Group G] [Group H] [Finite H] (f : H →* G) :
    Limits.IsZero (groupCohomology (Rep.res f (Rep.trivial ℤ G ℤ)) 1) := by
  refine Limits.IsZero.of_iso ?_ (groupCohomology.H1IsoOfIsTrivial (Rep.res f (Rep.trivial ℤ G ℤ)))
  haveI : Subsingleton (ModuleCat.of ℤ (Additive H →+ (Rep.res f (Rep.trivial ℤ G ℤ)))) := by
    change Subsingleton (Additive H →+ ℤ)
    exact ⟨fun a b => (addMonoidHom_int_eq_zero a).trans (addMonoidHom_int_eq_zero b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem map_top_injective {G : Type} [Group G] (A : Rep ℤ G) (n : ℕ) :
    Function.Injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom := by
  let eT : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom
  have key : groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n ≫
      groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A))) n = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := A) (n := n)
  have hleft : ∀ z : groupCohomology A n,
      (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype A))) n).hom
        ((groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom z) = z := by
    intro z
    have hz := congrArg (fun T => (ModuleCat.Hom.hom T) z) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hz
    exact hz
  exact Function.LeftInverse.injective hleft

end NumberField.PlaceDecomp.H3
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField.PlaceDecomp.H3"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField.PlaceDecomp"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion.NumberField"

open NumberField.PlaceDecomp.H3 in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (u : (Fin 3 → ↥(NumberField.PlaceDecomp.decomp E K w)) → Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hu : ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)).d 3 4).hom u = 0) :
    ∃ c : (Fin 2 → ↥(NumberField.PlaceDecomp.decomp E K w)) → Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ,
      ((inhomogeneousCochains (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)).d 2 3).hom c = u := by
  classical
  haveI : Fintype (↥(NumberField.PlaceDecomp.decomp E K w)) := Fintype.ofFinite _
  obtain ⟨u₀, h1, h2card, h2gen⟩ := NumberField.PlaceDecomp.exists_fundamentalClass_units_adicCompletion E K w
  haveI : Fintype (↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w)))) := Fintype.ofFinite _
  obtain ⟨e⟩ := Rep.nonempty_tateCohomology_trivial_iso_of_h1_h2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) u₀ h1
    (fun S => h2card S) h2gen ⊤ 1

  have hZ3top : Limits.IsZero (groupCohomology (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 3) := by
    have hZ1 := isZero_H1_trivial (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (G := (↥(NumberField.PlaceDecomp.decomp E K w)))
    exact Limits.IsZero.of_iso hZ1 e.symm
  have hZ3 : Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 3) := by
    have hzero : ∀ m : groupCohomology (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) 3, m = 0 := fun m => by
      have := congrArg (fun T => (ModuleCat.Hom.hom T) m) (hZ3top.eq_of_src (𝟙 _) 0)
      simpa using this
    haveI : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 3) :=
      ⟨fun a b => map_top_injective _ 3 ((hzero _).trans (hzero _).symm)⟩
    exact ModuleCat.isZero_of_subsingleton _
  exact exists_d_two_three_eq_of_isZero _ hZ3 u hu

end S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_inhomogeneousCochains_d_two_three_eq_adicCompletion (solution)
