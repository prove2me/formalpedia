-- Prove2me | solution 1 for M4aHerbrand.bijective_groupCohomology_map_toSIdeleClass
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/19260a0a-4dcf-570f-ae1a-389ec3caa909

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_M4aHerbrand_disjoint_unitIdelesTrivialOn_principalIdeles
import Theorems.Thm_M4aHerbrand_subsingleton_tateCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_tateδneg2_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply"
p2m_attr_erase "simp" "LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

set_option backward.isDefEq.respectTransparency false in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1)
    (hT : D.StabilizesUnitIdeles T)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup (𝓞 F) F T)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F),
      g • toSIdeleClass (𝓞 F) F T c = toSIdeleClass (𝓞 F) F T (D.classAct g c))
    (S : Subgroup (F ≃ₐ[E] F)) (n : ℕ) :
    Function.Bijective ((groupCohomology.functor ℤ S (n + 1)).map ((Rep.resFunctor S.subtype).map
      (toSIdeleClassRepHom T (toSIdeleClass_smul_of_descent D T hact hactS)))).hom := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Fintype S := Fintype.ofFinite S

  letI instU : MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T) :=
    { smul := fun g x => ⟨D.unitsAct g (x : (AdeleRing (𝓞 F) F)ˣ), hT g (x : (AdeleRing (𝓞 F) F)ˣ) x.2⟩
      one_smul := fun x => Subtype.ext (by
        change D.unitsAct 1 (x : (AdeleRing (𝓞 F) F)ˣ) = x
        rw [map_one]; rfl)
      mul_smul := fun g h x => Subtype.ext (by
        change D.unitsAct (g * h) (x : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g (D.unitsAct h (x : (AdeleRing (𝓞 F) F)ˣ))
        rw [map_mul]; rfl)
      smul_mul := fun g x y => Subtype.ext (map_mul (D.unitsAct g) (x : (AdeleRing (𝓞 F) F)ˣ) (y : (AdeleRing (𝓞 F) F)ˣ))
      smul_one := fun g => Subtype.ext (map_one (D.unitsAct g)) }
  have hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g (x : (AdeleRing (𝓞 F) F)ˣ) := fun _ _ => rfl

  let j : unitIdelesTrivialOn (𝓞 F) F T →* IdeleClassGroup (𝓞 F) F :=
    (QuotientGroup.mk' (principalIdeles (𝓞 F) F)).comp (unitIdelesTrivialOn (𝓞 F) F T).subtype
  have hj : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T), j (g • x) = g • j x := by
    intro g x
    rw [hact]
    rfl
  let ι : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T) ⟶
      Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) := repHomOfMulEquivariant j hj
  let φ : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) ⟶
      Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup (𝓞 F) F T) :=
    toSIdeleClassRepHom T (toSIdeleClass_smul_of_descent D T hact hactS)
  have hιφ : ∀ x, φ.hom (ι.hom x) = 0 := by
    intro x
    simp only [ι, φ, toSIdeleClassRepHom, repHomOfMulEquivariant_hom_apply, toMul_ofMul]
    change toSIdeleClass (𝓞 F) F T (QuotientGroup.mk ((Additive.toMul x : unitIdelesTrivialOn (𝓞 F) F T) :
      (AdeleRing (𝓞 F) F)ˣ)) = 1
    rw [toSIdeleClass_mk_eq_one_iff]
    exact unitIdelesTrivialOn_le_sClassKernel (𝓞 F) F T (Additive.toMul x).2

  let X : ShortComplex (Rep ℤ S) :=
    { X₁ := Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T))
      X₂ := Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
      X₃ := Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup (𝓞 F) F T))
      f := (Rep.resFunctor S.subtype).map ι
      g := (Rep.resFunctor S.subtype).map φ
      zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => hιφ x)) }

  have hinj : Function.Injective X.f.hom := fun x y hxy => by
    have hxy' : j (Additive.toMul x) = j (Additive.toMul y) := by
      first | exact hxy | simpa [X, ι] using hxy | simpa +zetaDelta [X, ι] using hxy
    have hq : ((Additive.toMul x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ)⁻¹ *
        (Additive.toMul y : unitIdelesTrivialOn (𝓞 F) F T) ∈ principalIdeles (𝓞 F) F := by
      rw [← QuotientGroup.eq]
      exact hxy'
    have h1 := (Subgroup.disjoint_def.1 (M4aHerbrand.disjoint_unitIdelesTrivialOn_principalIdeles F T))
      (mul_mem (inv_mem (Additive.toMul x).2) (Additive.toMul y).2) hq
    have : (Additive.toMul x : unitIdelesTrivialOn (𝓞 F) F T) = Additive.toMul y :=
      Subtype.ext (inv_mul_eq_one.1 h1)
    first | exact congrArg Additive.ofMul this | simpa using congrArg Additive.ofMul this | simpa +zetaDelta using congrArg Additive.ofMul this
  have hsurj : Function.Surjective X.g.hom := fun y => by
    obtain ⟨c, hc⟩ := toSIdeleClass_surjective (𝓞 F) F T (Additive.toMul y)
    exact ⟨Additive.ofMul c, by first | exact congrArg Additive.ofMul hc | simpa [X, φ, toSIdeleClassRepHom] using congrArg Additive.ofMul hc⟩
  have hker : ∀ x, X.g.hom x = 0 → ∃ u, X.f.hom u = x := fun x hx => by
    have hx' : toSIdeleClass (𝓞 F) F T (Additive.toMul x) = 1 := by
      first | exact hx | simpa [X, φ, toSIdeleClassRepHom] using hx | simpa +zetaDelta [X, φ, toSIdeleClassRepHom] using hx
    have hmem : Additive.toMul x ∈ (toSIdeleClass (𝓞 F) F T).ker := hx'
    rw [ker_toSIdeleClass] at hmem
    obtain ⟨u, hu, hux⟩ := hmem
    refine ⟨Additive.ofMul ⟨u, hu⟩, ?_⟩
    first | exact congrArg Additive.ofMul hux | simpa [X, ι, j] using congrArg Additive.ofMul hux | simpa +zetaDelta [X, ι, j] using congrArg Additive.ofMul hux
  have hrk : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact hιφ u
    · intro x hx
      obtain ⟨u, hu⟩ := hker x hx
      exact ⟨u, hu⟩
  haveI : Mono X.f := (Rep.mono_iff_injective _).2 hinj
  haveI : Epi X.g := (Rep.epi_iff_surjective _).2 hsurj

  have hSE : (X.map (groupCohomology.cochainsFunctor ℤ S)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
      { exact := by
          simp [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          erw [LinearMap.range_compLeft, LinearMap.ker_compLeft, hrk]
        mono_f := groupCohomology.cochainsMap_id_f_map_mono X.f i
        epi_g := groupCohomology.cochainsMap_id_f_map_epi X.g i }

  have hvan : ∀ m : ℕ, Limits.IsZero (groupCohomology X.X₁ (m + 1)) := by
    intro m
    have hs := M4aHerbrand.subsingleton_tateCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one
      E F D T hunr hactU S ((m + 1 : ℕ) : ℤ)
    rw [Rep.tateCohomology_ofNat_succ] at hs
    exact ModuleCat.isZero_of_subsingleton _

  have hmono : Mono ((groupCohomology.functor ℤ S (n + 1)).map X.g) :=
    (hSE.homology_exact₂ (n + 1)).mono_g ((hvan n).eq_of_src _ _)

  have hepi : Epi ((groupCohomology.functor ℤ S (n + 1)).map X.g) :=
    (hSE.homology_exact₃ (n + 1) (n + 2) rfl).epi_f ((hvan (n + 1)).eq_of_tgt _ _)
  exact ⟨(ModuleCat.mono_iff_injective _).1 hmono, (ModuleCat.epi_iff_surjective _).1 hepi⟩

end S_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass
end P2MW
export P2MW.S_M4aHerbrand_bijective_groupCohomology_map_toSIdeleClass (solution)
