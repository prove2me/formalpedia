-- Prove2me | solution 1 for NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/14b8562b-cc62-5977-a272-67956f4ce8cc

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
import Theorems.Thm_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one
import Theorems.Thm_NumberField_AdeleRing_valued_snd_smul_smul_eq
import Theorems.Thm_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open IsDedekindDomain NumberField CategoryTheory groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport
set_option linter.unusedSectionVars false

noncomputable section

namespace IdSupAux

variable {K : Type} [Field K] [NumberField K]

def ordHom (w : HeightOneSpectrum (𝓞 K)) : (w.adicCompletion K)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ))) : (w.adicCompletion K) →* WithZero (Multiplicative ℤ)))

theorem coe_ordHom (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletion K)ˣ) :
    ((ordHom w u : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = Valued.v (u : w.adicCompletion K) := by
  simp [ordHom]

def ordU (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletion K)ˣ) : ℤ := - Multiplicative.toAdd (ordHom w u)

theorem valued_eq_ordU (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletion K)ˣ) :
    Valued.v (u : w.adicCompletion K) = ((Multiplicative.ofAdd (-(ordU w u)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [← coe_ordHom]; simp [ordU]

theorem ordU_mul (w : HeightOneSpectrum (𝓞 K)) (u u' : (w.adicCompletion K)ˣ) : ordU w (u * u') = ordU w u + ordU w u' := by
  simp only [ordU, map_mul, toAdd_mul]; ring

theorem ordU_one (w : HeightOneSpectrum (𝓞 K)) : ordU w 1 = 0 := by simp [ordU]

theorem ordU_inv (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletion K)ˣ) : ordU w u⁻¹ = - ordU w u := by
  simp only [ordU, map_inv, toAdd_inv]

theorem ordU_eq_zero_iff (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletion K)ˣ) :
    ordU w u = 0 ↔ Valued.v (u : w.adicCompletion K) = 1 := by
  rw [valued_eq_ordU]
  constructor
  · intro h; simp [h]
  · intro h
    have : (Multiplicative.ofAdd (-(ordU w u)) : Multiplicative ℤ) = 1 := by exact_mod_cast h
    simpa using this

theorem ordU_eq_of_valued_eq {w w' : HeightOneSpectrum (𝓞 K)} (u : (w.adicCompletion K)ˣ) (u' : (w'.adicCompletion K)ˣ)
    (h : Valued.v (u : w.adicCompletion K) = Valued.v (u' : w'.adicCompletion K)) : ordU w u = ordU w' u' := by
  rw [valued_eq_ordU, valued_eq_ordU] at h
  have : (Multiplicative.ofAdd (-(ordU w u)) : Multiplicative ℤ) = Multiplicative.ofAdd (-(ordU w' u')) := by exact_mod_cast h
  simpa using this

def vv (y : (AdeleRing (𝓞 K) K)ˣ) : HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun w => ordU w (finPart w y)) (by
    refine (NumberField.AdeleRing.finite_setOf_valued_snd_ne_one K y).subset ?_
    intro w hw
    simp only [Function.mem_support, ne_eq, ordU_eq_zero_iff] at hw
    exact hw)

theorem vv_apply (y : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) : vv y w = ordU w (finPart w y) := rfl

theorem vv_mul (y y' : (AdeleRing (𝓞 K) K)ˣ) : vv (y * y') = vv y + vv y' := by
  ext w; simp only [vv_apply, map_mul, ordU_mul, Finsupp.add_apply]

theorem vv_one : vv (1 : (AdeleRing (𝓞 K) K)ˣ) = 0 := by
  ext w; simp only [vv_apply, map_one, ordU_one, Finsupp.coe_zero, Pi.zero_apply]

theorem vv_inv (y : (AdeleRing (𝓞 K) K)ˣ) : vv y⁻¹ = - vv y := by
  ext w; simp only [vv_apply, map_inv, ordU_inv, Finsupp.neg_apply]

theorem valued_finPart (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ) :
    Valued.v ((finPart w y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Valued.v (((y : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) := rfl

theorem mem_unitIdelesOutside_iff_vv (T : Set (HeightOneSpectrum (𝓞 K))) (y : (AdeleRing (𝓞 K) K)ˣ) :
    y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T ↔ ∀ w, w ∉ T → vv y w = 0 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [vv_apply, ordU_eq_zero_iff, valued_finPart]

theorem exists_vv_eq (m : HeightOneSpectrum (𝓞 K) →₀ ℤ) : ∃ q : (AdeleRing (𝓞 K) K)ˣ, vv q = m := by
  obtain ⟨q, hq⟩ := NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg K m
  refine ⟨q, Finsupp.ext fun w => ?_⟩
  have h := hq w
  rw [← valued_finPart, valued_eq_ordU] at h
  have : (Multiplicative.ofAdd (-(ordU w (finPart w q))) : Multiplicative ℤ) = Multiplicative.ofAdd (-(m w)) := by exact_mod_cast h
  have : -(ordU w (finPart w q)) = -(m w) := by simpa using this
  rw [vv_apply]; linarith

end IdSupAux

section Equivariance

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

theorem IdSupAux.vv_smul (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) (y : (AdeleRing (𝓞 K) K)ˣ) :
    IdSupAux.vv (g • y) = Finsupp.mapDomain (g • ·) (IdSupAux.vv y) := by
  ext w'
  have hinj : Function.Injective (fun w : HeightOneSpectrum (𝓞 K) => g • w) := MulAction.injective g
  obtain ⟨w, rfl⟩ : ∃ w, g • w = w' := ⟨g⁻¹ • w', smul_inv_smul g w'⟩
  rw [Finsupp.mapDomain_apply hinj, IdSupAux.vv_apply, IdSupAux.vv_apply]
  apply IdSupAux.ordU_eq_of_valued_eq
  rw [IdSupAux.valued_finPart, IdSupAux.valued_finPart]
  exact NumberField.AdeleRing.valued_snd_smul_smul_eq E K D hactI g y w

theorem IdSupAux.ordU_decomp_smul (w : HeightOneSpectrum (𝓞 K)) (s : ↥(NumberField.PlaceDecomp.decomp E K w)) (u : (w.adicCompletion K)ˣ) :
    IdSupAux.ordU w (s • u) = IdSupAux.ordU w u := by
  apply IdSupAux.ordU_eq_of_valued_eq
  rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.valued_smul]

end Equivariance

end

noncomputable section

namespace IdSupAux

section Generic

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem mapCocycles₂_apply_mk {A : Rep k H} {B : Rep k G} (F : G →* H) (Φ : Rep.res F A ⟶ B)
    (x : groupCohomology.cocycles₂ A) (g h : G) : groupCohomology.mapCocycles₂ F Φ x (g, h) = Φ.hom (x (F g, F h)) := rfl

theorem hom_d₁₂_apply {X Y : Rep k G} (Φ : X ⟶ Y) (b : G → X) (g h : G) :
    Φ.hom ((groupCohomology.d₁₂ X).hom b (g, h)) = (groupCohomology.d₁₂ Y).hom (fun g => Φ.hom (b g)) (g, h) := by
  simp only [groupCohomology.d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply]

theorem mem_cocycles₂_of_injective {X Y : Rep k G} (Φ : X ⟶ Y) (hΦ : Function.Injective Φ.hom) (z : G × G → X)
    (hz : (fun p => Φ.hom (z p)) ∈ groupCohomology.cocycles₂ Y) : z ∈ groupCohomology.cocycles₂ X := by
  rw [groupCohomology.mem_cocycles₂_iff] at hz ⊢
  intro g h j
  apply hΦ
  have := hz g h j
  simp only [map_add, Rep.hom_comm_apply] at this ⊢
  exact this

end Generic

section Idele

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

abbrev toI [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (a : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ := Additive.toMul (α := (AdeleRing (𝓞 K) K)ˣ) a

abbrev toL (w : HeightOneSpectrum (𝓞 K))
    (a : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) : (w.adicCompletion K)ˣ :=
  Additive.toMul (α := (w.adicCompletion K)ˣ) a

def vvA [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ] :
    (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) →+ (HeightOneSpectrum (𝓞 K) →₀ ℤ) where
  toFun a := vv (K := K) (toI (E := E) a)
  map_zero' := vv_one
  map_add' a a' := by
    change vv (K := K) (toI (E := E) a * toI (E := E) a') = _
    exact vv_mul _ _

theorem vvA_apply [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (a : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) : vvA (E := E) a = vv (toI (E := E) a) := rfl

theorem vvA_ofMul [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ] (y : (AdeleRing (𝓞 K) K)ˣ) :
    vvA (E := E) (Additive.ofMul y) = vv y := rfl

theorem vvA_ρ (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) (a : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) :
    vvA ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g a) = Finsupp.mapDomain (g • ·) (vvA a) := by
  rw [vvA_apply, vvA_apply]
  have : toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g a) = g • toI (E := E) a := by
    erw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
  rw [this]
  exact vv_smul D hactI g (toI (E := E) a)

def ordA (w : HeightOneSpectrum (𝓞 K)) :
    (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) →+ ℤ where
  toFun a := ordU w (toL (E := E) w a)
  map_zero' := ordU_one w
  map_add' a a' := by
    change ordU w (toL (E := E) w a * toL (E := E) w a') = _
    exact ordU_mul _ _ _

theorem ordA_apply (w : HeightOneSpectrum (𝓞 K))
    (a : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) : ordA (E := E) w a = ordU w (toL (E := E) w a) := rfl

theorem ordA_ρ (w : HeightOneSpectrum (𝓞 K)) (s : ↥(NumberField.PlaceDecomp.decomp E K w))
    (a : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) :
    ordA w ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ).ρ s a) = ordA w a := by
  rw [ordA_apply, ordA_apply]
  have : toL w ((Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ).ρ s a) = s • toL (E := E) w a := by
    erw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
  rw [this]
  exact ordU_decomp_smul w s _

end Idele

end IdSupAux

end

section Main

open IdSupAux

theorem IdSup.exists_eq_of_mem (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (a : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (ha : toI a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) :
    ∃ m : NumberField.SIdele.obj E K S, Ψ.hom m = a := by
  obtain ⟨m, hm⟩ := (hΨrange (toI a)).2 ha
  exact ⟨m, hm⟩

theorem IdSup.mem_of_eq (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (m : NumberField.SIdele.obj E K S) :
    toI (Ψ.hom m) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} :=
  (hΨrange (toI (Ψ.hom m))).1 ⟨m, rfl⟩

set_option maxHeartbeats 12800000 in

theorem IdSup.exists_of_forall (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (c : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K))) →
      H2π _ (groupCohomology.mapCocycles₂ (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) c) = 0) :
    ∃ z : groupCohomology.cocycles₂ (NumberField.SIdele.obj E K S),
      H2π _ (groupCohomology.mapCocycles₂ (MonoidHom.id (K ≃ₐ[E] K)) Ψ z) = H2π _ c := by
  classical
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  have hT : ∀ (g : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)),
      (g • w) ∈ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K))) ↔ w ∈ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K))) := by
    intro g w
    simp only [Set.mem_setOf_eq, NumberField.PlaceTransport.under_smul]

  let P : HeightOneSpectrum (𝓞 K) → Prop := fun w => w ∉ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K)))
  let V : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) →+ (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
    (Finsupp.filterAddHom P).comp vvA
  have hVapply : ∀ a, V a = (vvA a).filter P := fun a => rfl
  have hfilt_map : ∀ (g : K ≃ₐ[E] K) (m : HeightOneSpectrum (𝓞 K) →₀ ℤ),
      (Finsupp.mapDomain (g • ·) m).filter P = Finsupp.mapDomain (g • ·) (m.filter P) := by
    intro g m
    ext w'
    obtain ⟨w, rfl⟩ : ∃ w, g • w = w' := ⟨g⁻¹ • w', smul_inv_smul g w'⟩
    have hinj : Function.Injective (fun w : HeightOneSpectrum (𝓞 K) => g • w) := MulAction.injective g
    rw [Finsupp.mapDomain_apply hinj, Finsupp.filter_apply, Finsupp.filter_apply, Finsupp.mapDomain_apply hinj]
    have : P (g • w) ↔ P w := not_congr (hT g w)
    by_cases hw : P w
    · rw [if_pos hw, if_pos (this.2 hw)]
    · rw [if_neg hw, if_neg (fun h => hw (this.1 h))]
  have hVρ : ∀ (g : K ≃ₐ[E] K) a, V ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g a) = Finsupp.mapDomain (g • ·) (V a) := by
    intro g a
    rw [hVapply, hVapply, vvA_ρ D hactI, hfilt_map]
  let ν : (K ≃ₐ[E] K) → (K ≃ₐ[E] K) → HeightOneSpectrum (𝓞 K) →₀ ℤ := fun g h => V (c (g, h))
  have hνapply : ∀ (g h : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)), P w → ν g h w = ordU w (finPart w (toI (c (g, h)))) := by
    intro g h w hw
    change ((vvA (c (g, h))).filter P) w = _
    rw [Finsupp.filter_apply_pos P _ hw, vvA_apply, vv_apply]
  have hν : ∀ g h j : K ≃ₐ[E] K, Finsupp.mapDomain (g • ·) (ν h j) - ν (g * h) j + ν g (h * j) - ν g h = 0 := by
    intro g h j
    have hc := (groupCohomology.mem_cocycles₂_def (A := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) c).1 c.2 g h j
    have := congrArg V hc
    rw [map_sub, map_add, map_sub, hVρ, map_zero] at this
    exact this

  have hloc : ∀ w₀ : HeightOneSpectrum (𝓞 K), ∃ β : ↥(MulAction.stabilizer (K ≃ₐ[E] K) w₀) → ℤ,
      ∀ s t : ↥(MulAction.stabilizer (K ≃ₐ[E] K) w₀), ν s t w₀ = β s + β t - β (s * t) := by
    intro w₀
    by_cases hw₀ : P w₀
    · have h0 := hsupp w₀ hw₀
      rw [groupCohomology.H2π_eq_zero_iff] at h0
      obtain ⟨b, hb⟩ := h0
      have hsd : MulAction.stabilizer (K ≃ₐ[E] K) w₀ = NumberField.PlaceDecomp.decomp E K w₀ :=
        NumberField.PlaceTransport.stabilizer_eq_decomp E K w₀
      let ι : ↥(MulAction.stabilizer (K ≃ₐ[E] K) w₀) → ↥(NumberField.PlaceDecomp.decomp E K w₀) :=
        fun s => ⟨s.1, hsd ▸ s.2⟩
      have hι : ∀ s : ↥(MulAction.stabilizer (K ≃ₐ[E] K) w₀), ((ι s : ↥(NumberField.PlaceDecomp.decomp E K w₀)) : K ≃ₐ[E] K) = s := fun s => rfl
      have hιmul : ∀ s t : ↥(MulAction.stabilizer (K ≃ₐ[E] K) w₀), ι (s * t) = ι s * ι t := fun s t => Subtype.ext rfl
      refine ⟨fun s => ordA w₀ (b (ι s)), fun s t => ?_⟩
      have key := congrFun hb (ι s, ι t)
      rw [groupCohomology.d₁₂_hom_apply] at key
      have key' := congrArg (ordA (E := E) w₀) key
      rw [map_add, map_sub, ordA_ρ] at key'

      have hfin : ordA w₀ ((groupCohomology.mapCocycles₂ (NumberField.PlaceDecomp.decomp E K w₀).subtype (prG w₀) c) (ι s, ι t)) = ν s t w₀ := by
        rw [hνapply _ _ _ hw₀, mapCocycles₂_apply_mk, ordA_apply]
        have := hprG w₀ (toI (c ((s : K ≃ₐ[E] K), (t : K ≃ₐ[E] K))))
        change ordU w₀ (toL w₀ ((prG w₀).hom (Additive.ofMul (toI (c (↑s, ↑t)))))) = _
        rw [this]
        rfl
      rw [← hfin, ← key']
      dsimp only
      rw [hιmul]
      ring
    · refine ⟨fun _ => 0, fun s t => ?_⟩
      change ((vvA (c (s, t))).filter P) w₀ = _
      rw [Finsupp.filter_apply_neg P _ hw₀]; ring

  obtain ⟨μ, hμ⟩ := groupCohomology.exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer ν hν hloc

  choose b hb using fun g : K ≃ₐ[E] K => exists_vv_eq (K := K) (μ g)
  let β₁ : (K ≃ₐ[E] K) → Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ := fun g => Additive.ofMul (b g)
  have hVβ : ∀ g, vvA (β₁ g) = μ g := fun g => by
    change vv (b g) = μ g
    exact hb g
  let c' : (K ≃ₐ[E] K) × (K ≃ₐ[E] K) → Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ :=
    fun p => c p - (groupCohomology.d₁₂ _).hom β₁ p
  have hc'mem : c' ∈ groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) := by
    change (⇑c - (groupCohomology.d₁₂ _).hom β₁) ∈ groupCohomology.cocycles₂ _
    exact Submodule.sub_mem _ c.2 (groupCohomology.d₁₂_apply_mem_cocycles₂ β₁)

  have hc'J : ∀ p, toI (c' p) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
    rintro ⟨g, h⟩
    refine (mem_unitIdelesOutside_iff_vv _ _).2 fun w hw => ?_
    have hval : vvA (c' (g, h)) = vvA (c (g, h)) - (Finsupp.mapDomain (g • ·) (μ h) - μ (g * h) + μ g) := by
      change vvA (c (g, h) - (groupCohomology.d₁₂ _).hom β₁ (g, h)) = _
      rw [map_sub, groupCohomology.d₁₂_hom_apply, map_add, map_sub, vvA_ρ D hactI, hVβ, hVβ, hVβ]
    have h1 : vv (toI (c' (g, h))) w = vvA (c' (g, h)) w := rfl
    have h2 : vvA (c (g, h)) w = ν g h w := by
      change _ = ((vvA (c (g, h))).filter P) w
      rw [Finsupp.filter_apply_pos P _ hw]
    rw [h1, hval, Finsupp.sub_apply, h2, hμ g h, sub_self]

  choose z₀ hz₀ using fun p => IdSup.exists_eq_of_mem E K S D hactI Ψ hΨinj hΨrange (c' p) (hc'J p)
  have hz₀mem : z₀ ∈ groupCohomology.cocycles₂ (NumberField.SIdele.obj E K S) := by
    apply mem_cocycles₂_of_injective Ψ hΨinj
    have : (fun p => Ψ.hom (z₀ p)) = c' := funext hz₀
    rw [this]; exact hc'mem
  refine ⟨⟨z₀, hz₀mem⟩, ?_⟩
  have hmc : groupCohomology.mapCocycles₂ (MonoidHom.id (K ≃ₐ[E] K)) Ψ ⟨z₀, hz₀mem⟩ = ⟨c', hc'mem⟩ := by
    apply groupCohomology.cocycles₂_ext
    intro g h
    rw [mapCocycles₂_apply_mk]
    exact hz₀ (g, h)
  rw [hmc, groupCohomology.H2π_eq_iff]
  refine ⟨-β₁, ?_⟩
  rw [map_neg]
  funext p
  change -((groupCohomology.d₁₂ _).hom β₁ p) = (c p - (groupCohomology.d₁₂ _).hom β₁ p) - c p
  abel

set_option maxHeartbeats 12800000 in

theorem IdSup.eq_zero_of_map_eq_zero (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (zc : groupCohomology.cocycles₂ (NumberField.SIdele.obj E K S))
    (hz : H2π _ (groupCohomology.mapCocycles₂ (MonoidHom.id (K ≃ₐ[E] K)) Ψ zc) = 0) :
    H2π _ zc = 0 := by
  classical
  rw [groupCohomology.H2π_eq_zero_iff] at hz
  obtain ⟨e, he⟩ := hz
  have hde : ∀ g h : K ≃ₐ[E] K, toI (e g) * (g • toI (e h)) / toI (e (g * h)) ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
    intro g h
    have key := congrFun he (g, h)
    rw [groupCohomology.d₁₂_hom_apply, mapCocycles₂_apply_mk] at key
    have hρ : toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g (e h)) = g • toI (e h) := by
      erw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
    have heq : toI (e g) * (g • toI (e h)) / toI (e (g * h)) =
        toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g (e h) - e (g * h) + e g) := by
      change _ = toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g (e h)) * (toI (e (g * h)))⁻¹ * toI (e g)
      rw [hρ, div_eq_mul_inv, mul_comm (toI (e g)) (g • toI (e h)), mul_right_comm]
    rw [heq, key]
    exact IdSup.mem_of_eq E K S D hactI Ψ hΨinj hΨrange _
  have hq := NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem E K S D hactI
    (fun g => toI (e g)) hde
  obtain ⟨q, hq⟩ := hq
  let qA : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ := Additive.ofMul q
  have hqA : toI qA = q := rfl
  have hqAρ : ∀ g : K ≃ₐ[E] K, toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g qA) = g • q := by
    intro g; erw [Rep.ofMulDistribMulAction_ρ_apply_apply]; rfl
  let e' : (K ≃ₐ[E] K) → Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ :=
    fun g => e g - ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g qA - qA)
  have he'J : ∀ g, toI (e' g) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
    intro g
    have heq : toI (e' g) = toI (e g) * (g • q / q)⁻¹ := by
      change toI (e g) * (toI ((Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).ρ g qA) * (toI qA)⁻¹)⁻¹ = _
      rw [hqAρ, hqA, div_eq_mul_inv]
    rw [heq]; exact hq g
  choose m hm using fun g => IdSup.exists_eq_of_mem E K S D hactI Ψ hΨinj hΨrange (e' g) (he'J g)
  have hde' : ∀ g h, (groupCohomology.d₁₂ _).hom e' (g, h) = (groupCohomology.d₁₂ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)).hom e (g, h) := by
    intro g h
    simp only [groupCohomology.d₁₂_hom_apply, e', map_sub]
    rw [← Module.End.mul_apply, ← map_mul]
    abel
  rw [groupCohomology.H2π_eq_zero_iff]
  refine ⟨m, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  apply hΨinj
  rw [hom_d₁₂_apply]
  have : (fun g => Ψ.hom (m g)) = e' := funext hm
  rw [this, hde']
  have key := congrFun he (g, h)
  rw [mapCocycles₂_apply_mk] at key
  simpa using key

end Main

open IdSupAux in
set_option maxHeartbeats 6400000 in
theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Ψ : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)
    (hΨinj : Function.Injective Ψ.hom)
    (hΨrange : ∀ y : (AdeleRing (𝓞 K) K)ˣ, (∃ x, Ψ.hom x = Additive.ofMul y) ↔
      y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x = 0) :
    ∃! z : groupCohomology (NumberField.SIdele.obj E K S) 2,
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2).hom z = x := by
  classical
  have hoff : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K))) →
      ∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal := by
    intro w hw v hv h
    apply hw
    simp only [Set.mem_setOf_eq]
    have : w.under (𝓞 E) = v := HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact h)
    rwa [this]
  have hinj2 : ∀ z : groupCohomology (NumberField.SIdele.obj E K S) 2,
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2).hom z = 0 → z = 0 := by
    intro z
    induction z using groupCohomology.H2_induction_on with
    | h zc =>
    intro hz
    apply IdSup.eq_zero_of_map_eq_zero E K S D hactI Ψ hΨinj hΨrange zc
    rw [← groupCohomology.H2π_comp_map_apply]
    exact hz
  induction x using groupCohomology.H2_induction_on with
  | h c =>
  have hs : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ ({w | w.under (𝓞 E) ∈ S} : Set (HeightOneSpectrum (𝓞 K))) →
      H2π _ (groupCohomology.mapCocycles₂ (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) c) = 0 := by
    intro w hw
    rw [← groupCohomology.H2π_comp_map_apply]
    exact hsupp w (hoff w hw)
  obtain ⟨z, hz⟩ := IdSup.exists_of_forall E K S D hactI Ψ hΨinj hΨrange prG hprG c hs
  refine ⟨H2π _ z, ?_, fun z' hz' => ?_⟩
  · change (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2) (H2π _ z) = H2π _ c
    rw [groupCohomology.H2π_comp_map_apply, hz]
  · have h0 : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2).hom (z' - H2π _ z) = 0 := by
      rw [map_sub, hz', sub_eq_zero]
      change H2π _ c = (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2) (H2π _ z)
      rw [groupCohomology.H2π_comp_map_apply, hz]
    exact sub_eq_zero.1 (hinj2 _ h0)

end S_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero
end P2MW
export P2MW.S_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero (solution)
