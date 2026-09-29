-- Prove2me | solution 1 for LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cf9eba5c-e8d3-5d09-bc0a-1e6efb2386f2

import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree
import Theorems.Thm_M4aKummer_normClassIndex_dvd_card_aut_of_isSolvable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

namespace Deep
namespace NTSupply
p2m_export "Deep.NTSupply" "coprimeToModulus narrowRaySubgroup raySymbol hasFiniteMulSupport_raySymbol_factors raySymbolUnitsHom raySymbolHom raySymbolHom_apply primeUnit primeUnit_val primeUnit_mem_coprimeToModulus raySymbol_primeUnit"
p2m_open "Deep.NTSupply Deep"
end Deep.NTSupply

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"
end HeckeCharacter

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P0
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P5
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P5

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open NumberField IsDedekindDomain

open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

private theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

variable [Finite G] [Algebra.IsInvariant R S G]

private theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

private theorem arithFrobAt_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

private theorem eq_artinFrob_of_isArithFrobAt [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (𝓞 M)} [Q.IsPrime]
    (H : IsArithFrobAt (𝓞 K) σ Q) (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) : σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← arithFrobAt_eq_artinFrob K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end Artin

section Restrict

variable (K M M' : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field M'] [NumberField M']
  [Algebra K M] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M] [IsGalois K M']

private scoped instance : IsScalarTower (𝓞 K) (𝓞 M) (𝓞 M') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    refine RingOfIntegers.ext ?_
    show algebraMap K M' (x : K) = algebraMap M M' (algebraMap (𝓞 K) (𝓞 M) x : M)
    rw [show (algebraMap (𝓞 K) (𝓞 M) x : M) = algebraMap K M (x : K) from rfl, ← IsScalarTower.algebraMap_apply K M M']

private theorem isArithFrobAt_restrictNormal (τ : M' ≃ₐ[K] M') (Q' : Ideal (𝓞 M')) (H : IsArithFrobAt (𝓞 K) τ Q') :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom M τ) (Q'.under (𝓞 M)) := by
  intro x
  have hcard : Nat.card (𝓞 K ⧸ (Q'.under (𝓞 M)).under (𝓞 K)) = Nat.card (𝓞 K ⧸ Q'.under (𝓞 K)) := by
    rw [Ideal.under_under]
  have hkey : algebraMap (𝓞 M) (𝓞 M') ((AlgEquiv.restrictNormalHom M τ) • x) = τ • algebraMap (𝓞 M) (𝓞 M') x := by
    refine RingOfIntegers.ext ?_
    show algebraMap M M' ((τ.restrictNormal M) (x : M)) = τ (algebraMap M M' (x : M))
    exact AlgEquiv.restrictNormal_commutes τ M (x : M)
  rw [hcard, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
  erw [hkey]
  exact H (algebraMap (𝓞 M) (𝓞 M') x)

private theorem restrictNormal_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K))
    (hI : ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    AlgEquiv.restrictNormalHom M (artinFrob K M' v) = artinFrob K M v := by
  have H := isArithFrobAt_restrictNormal K M M' (artinFrob K M' v) (primeAbove K M' v) (isArithFrobAt_artinFrob K M' v)
  haveI : ((primeAbove K M' v).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove K M' v)
  refine eq_artinFrob_of_isArithFrobAt K M v H ?_ hI
  rw [Ideal.under_under, under_primeAbove]

end Restrict

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply"

open scoped IsMulCommutative nonZeroDivisors

section Finite

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E))
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    fracRelNormUnit k E (primeUnit E w)
      = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
            FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

set_option maxHeartbeats 3200000

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (placeUnder' k E w)
          ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal) := by
  exact fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in

private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in

private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

end Carriers
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.HeckeCharacter"

private theorem relNormCTM_range_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    (relNormCTM K L 𝔣).range ≤ (artinSymbol K L 𝔣).ker := by
  rw [MonoidHom.range_le_ker_iff]
  apply MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top L (modulusExt K L 𝔣))
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K L 𝔣 w).mp h)
  show artinSymbol K L 𝔣 (relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩) = 1
  rw [show relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩
        = (⟨primeUnit K (placeUnder' K L w), primeUnit_mem_coprimeToModulus K hv⟩
            : ↥(coprimeToModulus K 𝔣)) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal from
      Subtype.ext (relNormCTM_primeUnit K L hw),
    map_pow, artinSymbol_prime K L hv]
  exact hfrob w hv

end Pincer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

omit [NumberField K] [IsGalois K L] in

private theorem admissibleExpOfDegree_pos (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    0 < NumberField.NormIndex.admissibleExpOfDegree K n v :=
  Nat.add_pos_left Nat.one_pos _

omit [NumberField L] [IsGalois K L] in

private theorem dvd_of_isAdmissibleModulusOfDegree {n : ℕ} {𝔣 : Ideal (𝓞 K)} (h : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔣)
    {v : HeightOneSpectrum (𝓞 K)} (hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) : v.asIdeal ∣ 𝔣 :=
  dvd_trans (dvd_pow_self _ (admissibleExpOfDegree_pos K n v).ne') (h.2 v hv)

omit [NumberField L] [IsGalois K L] in

private theorem inertia_eq_bot_of_isAdmissibleModulusOfDegree {n : ℕ} {𝔣 : Ideal (𝓞 K)} (h : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔣)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥ :=
  not_ne_iff.mp fun hne => hv (dvd_of_isAdmissibleModulusOfDegree K L h hne)

omit [NumberField L] [IsGalois K L] in

private theorem isAdmissibleModulusOfDegree_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) {𝔣 : Ideal (𝓞 K)}
    (h : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔣) : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L m 𝔣 := by
  have hm : m ≠ 0 := ne_zero_of_dvd_ne_zero hn hmn
  refine ⟨h.1, fun v hv => dvd_trans (pow_dvd_pow _ ?_) (h.2 v hv)⟩
  unfold NumberField.NormIndex.admissibleExpOfDegree
  refine Nat.add_le_add_left ?_ 1
  refine (Finset.sum_le_sum fun p _ => ?_).trans (Finset.sum_le_sum_of_subset (Nat.primeFactors_mono hmn hn))
  exact Nat.mul_le_mul_right _ (Nat.succ_le_succ ((Nat.factorization_le_iff_dvd hm hn).mpr hmn p))

end Admissible
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Hfrob

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.HeckeCharacter"

attribute [local instance] Ideal.Quotient.field

private theorem artinFrob_pow_inertiaDeg_eq_one (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    artinFrob K L v ^ v.asIdeal.inertiaDeg' w.asIdeal = 1 := by

  have hmem : artinFrob K L v ∈ MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v) :=
    (isArithFrobAt_artinFrob K L v).mem_stabilizer
  haveI hwv' : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 L ⧸ primeAbove K L v) :=
    Ideal.finiteQuotientOfFreeOfNeBot (primeAbove K L v) (primeAbove_ne_bot K L v)

  have hcard : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v))
      = v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal
        (primeAbove K L v),
      hI, Subgroup.card_bot, one_mul,
      Ideal.inertiaDegIn_eq_inertiaDeg (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal,
      ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal]
  have := pow_card_eq_one'
    (G := ↥(MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v))) (x := ⟨_, hmem⟩)
  rw [hcard] at this
  exact Subtype.ext_iff.mp this

private theorem artinFrob_placeUnder_pow_inertiaDeg_eq_one (w : HeightOneSpectrum (𝓞 L))
    (hI : (primeAbove K L (placeUnder' K L w)).inertia (L ≃ₐ[K] L) = ⊥) :
    artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1 :=
  artinFrob_pow_inertiaDeg_eq_one K L (placeUnder' K L w) w (placeUnder'_asIdeal K L w).symm hI

end Hfrob
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.HeckeCharacter IntermediateField"

attribute [local instance] Ideal.Quotient.field

section AdmLayer

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

private theorem inertia_ne_bot_iff_ramificationIdxIn_ne_one (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K M v).inertia (M ≃ₐ[K] M) ≠ ⊥ ↔ v.asIdeal.ramificationIdxIn (𝓞 M) ≠ 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal (primeAbove K M v), ne_eq, ne_eq,
    Subgroup.card_eq_one]

private theorem inertia_eq_bot_of_isAdmissibleModulusOfDegree_of_not_under_dvd {n : ℕ} {𝔣 : Ideal (𝓞 K)}
    (h𝔣 : NumberField.NormIndex.IsAdmissibleModulusOfDegree K M n 𝔣)
    (P : Ideal (𝓞 M)) [hPm : P.IsMaximal] (hP : ¬ P.under (𝓞 K) ∣ 𝔣) : P.inertia (M ≃ₐ[K] M) = ⊥ := by
  have hPne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField M)
  let p₀ : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), (hPm.under (𝓞 K)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (hPm.under (𝓞 K)) (RingOfIntegers.not_isField K)⟩
  have hI0 : (primeAbove K M p₀).inertia (M ≃ₐ[K] M) = ⊥ := inertia_eq_bot_of_isAdmissibleModulusOfDegree K M h𝔣 p₀ hP
  have he : p₀.asIdeal.ramificationIdxIn (𝓞 M) = 1 := by
    by_contra he
    exact (inertia_ne_bot_iff_ramificationIdxIn_ne_one K M p₀).mpr he hI0
  haveI : P.LiesOver p₀.asIdeal := ⟨rfl⟩
  haveI : p₀.asIdeal.IsMaximal := p₀.isMaximal
  haveI : Finite (𝓞 K ⧸ p₀.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot p₀.asIdeal p₀.ne_bot
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) p₀.asIdeal P
  rwa [he, Subgroup.card_eq_one] at hc

variable [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M)

private theorem isGalois_layer : IsGalois K F :=
  IsGalois.of_algEquiv (IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup F))

omit [NumberField K] [NumberField M] in

private theorem isMulCommutative_gal_layer [IsGalois K F] : IsMulCommutative (F ≃ₐ[K] F) :=
  ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M a
    obtain ⟨b, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M b
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩

private theorem ramificationIdxIn_ne_one_of_layer (v : HeightOneSpectrum (𝓞 K))
    (h : v.asIdeal.ramificationIdxIn (𝓞 F) ≠ 1) : v.asIdeal.ramificationIdxIn (𝓞 M) ≠ 1 := by
  haveI := isGalois_layer K M F
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have htower := Ideal.ramificationIdxIn_mul_ramificationIdxIn' (p := v.asIdeal) (primeAbove K F v) (F ≃ₐ[K] F) (𝓞 M)
    (M ≃ₐ[K] M) (M ≃ₐ[F] M)
  intro h1
  rw [h1] at htower
  exact h (Nat.eq_one_of_mul_eq_one_right htower)

private theorem isAdmissibleModulusOfDegree_layer {n : ℕ} {𝔣 : Ideal (𝓞 K)} (h : NumberField.NormIndex.IsAdmissibleModulusOfDegree K M n 𝔣) :
    NumberField.NormIndex.IsAdmissibleModulusOfDegree K F n 𝔣 := by
  haveI := isGalois_layer K M F
  refine ⟨h.1, fun v hv => h.2 v ?_⟩
  rw [inertia_ne_bot_iff_ramificationIdxIn_ne_one] at hv ⊢
  exact ramificationIdxIn_ne_one_of_layer K M F v hv

end AdmLayer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section Restrict

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] (M : IntermediateField K L)

private theorem restrictNormalHom_artinSymbol [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    {n : ℕ} (hadmM : NumberField.NormIndex.IsAdmissibleModulusOfDegree K M n 𝔣) (x : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K L 𝔣 x) = artinSymbol K M 𝔣 x := by
  suffices h : (AlgEquiv.restrictNormalHom M).comp (artinSymbol K L 𝔣) = artinSymbol K M 𝔣 from DFunLike.congr_fun h x
  refine MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top K 𝔣) ?_
  rintro _ ⟨v, hv, rfl⟩
  show AlgEquiv.restrictNormalHom M (artinSymbol K L 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩)
    = artinSymbol K M 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩
  rw [artinSymbol_prime K L hv, artinSymbol_prime K M hv]
  refine restrictNormal_artinFrob K M L v ?_
  haveI : ((primeAbove K L v).under (𝓞 M)).IsMaximal := (primeAbove_isMaximal K L v).under (𝓞 M)
  refine inertia_eq_bot_of_isAdmissibleModulusOfDegree_of_not_under_dvd K M hadmM _ ?_
  rw [Ideal.under_under, under_primeAbove]
  exact hv

end Restrict
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section PincerPair

variable {I G : Type*} [CommGroup I] [Group G] [Finite G]

private theorem ker_eq_of_le_of_surjective_of_index_dvd (ω : I →* G) (𝔑 : Subgroup I) (hle : 𝔑 ≤ ω.ker)
    (honto : Function.Surjective ω) (hidx : 𝔑.index ∣ Nat.card G) : ω.ker = 𝔑 := by
  have hker : ω.ker.index = Nat.card G := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr honto, Subgroup.card_top]
  have hne : ω.ker.index ≠ 0 := by
    rw [hker]
    exact (Nat.card_pos (α := G)).ne'
  have hdvd : 𝔑.index ∣ ω.ker.index := by
    rw [hker]
    exact hidx
  have heq : 𝔑.index = ω.ker.index := Nat.dvd_antisymm hdvd (Subgroup.index_dvd_of_le hle)
  have hmul := Subgroup.relIndex_mul_index hle
  rw [heq, mul_eq_right₀ hne] at hmul
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hmul) hle

end PincerPair
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section Inequalities

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem fracRelNormUnit_eq_under :
    fracRelNormUnit K M = raySymbolUnitsHom M (fun w : HeightOneSpectrum (𝓞 M) =>
      primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) := rfl

private theorem coe_relNormCTM_eq_fracRelNormUnit {𝔠 : Ideal (𝓞 K)} (Y : ↥(coprimeToModulus M (modulusExt K M 𝔠))) :
    ((relNormCTM K M 𝔠 Y : ↥(coprimeToModulus K 𝔠)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = fracRelNormUnit K M Y := rfl

private theorem range_relNormCTM_eq_under (𝔣 : Ideal (𝓞 K)) :
    (relNormCTM K M 𝔣).range =
      ((coprimeToModulus M (𝔣.map (algebraMap (𝓞 K) (𝓞 M)))).map (raySymbolUnitsHom M (fun w : HeightOneSpectrum (𝓞 M) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣) := by
  rw [← fracRelNormUnit_eq_under]
  ext x
  simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : (FractionalIdeal ((𝓞 M)⁰) M)ˣ), y.2, (coe_relNormCTM_eq_fracRelNormUnit K M y).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, Subtype.ext (by rw [coe_relNormCTM_eq_fracRelNormUnit]; exact hzx)⟩

variable [IsGalois K M]

private theorem secondInequalityCTM_pair [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) : SecondInequalityCTM K M 𝔣 := by
  haveI : Group.IsSolvable (M ≃ₐ[K] M) := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  unfold SecondInequalityCTM
  rw [normRaySubgroup, range_relNormCTM_eq_under]
  exact M4aKummer.normClassIndex_dvd_card_aut_of_isSolvable K M 𝔣

variable [IsMulCommutative (M ≃ₐ[K] M)]

end Inequalities
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers normRaySubgroup SecondInequalityCTM primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Separation

private theorem eq_one_of_pow_eq_one_of_forall_pow_ordCompl_eq_one {G : Type*} [Group G] {n : ℕ} (hn : n ≠ 0)
    {g : G} (hg : g ^ n = 1) (h : ∀ ℓ ∈ n.primeFactors, g ^ (n / ℓ ^ n.factorization ℓ) = 1) : g = 1 := by
  rw [← orderOf_eq_one_iff]
  by_contra h1
  have hp : (orderOf g).minFac.Prime := Nat.minFac_prime h1
  have hmem : (orderOf g).minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, (Nat.minFac_dvd _).trans (orderOf_dvd_of_pow_eq_one hg), hn⟩
  exact Nat.not_dvd_ordCompl hp hn ((Nat.minFac_dvd _).trans (orderOf_dvd_of_pow_eq_one (h _ hmem)))

end Separation
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

section Layers

private def layerField (K L : Type*) [Field K] [Field L] [Algebra K L] [IsMulCommutative (L ≃ₐ[K] L)] (m : ℕ) :
    IntermediateField K L :=
  IntermediateField.fixedField (powMonoidHom m : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L)).ker

private theorem pow_artinSymbol_eq_one_of_mem_ray_and_pow_mem_range (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔣 : Ideal (𝓞 K)) {n : ℕ} (hn : n ≠ 0) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔣)
    (ℓ k m : ℕ) (hℓ : ℓ.Prime) (hk : ℓ ^ k ∣ n) (hpow : ∀ g : L ≃ₐ[K] L, (g ^ (ℓ ^ k)) ^ m = 1) :
    (∀ x : ↥(coprimeToModulus K 𝔣), x ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) →
        artinSymbol K L 𝔣 x ^ m = 1) ∧
      ∀ g : L ≃ₐ[K] L, g ^ m ∈ (artinSymbol K L 𝔣).range := by
  haveI hGal : IsGalois K (layerField K L m) := isGalois_layer K L _
  haveI hComm : IsMulCommutative (layerField K L m ≃ₐ[K] layerField K L m) := isMulCommutative_gal_layer K L _
  have hres : ∀ g : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom (layerField K L m) g = 1 ↔ g ^ m = 1 := fun g => by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    unfold layerField
    rw [IntermediateField.fixingSubgroup_fixedField, MonoidHom.mem_ker, powMonoidHom_apply]
  have hexpM : ∀ x : layerField K L m ≃ₐ[K] layerField K L m, x ^ (ℓ ^ k) = 1 := fun x => by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L x
    rw [← map_pow]
    exact (hres _).mpr (hpow g)
  have hadmM : NumberField.NormIndex.IsAdmissibleModulusOfDegree K (layerField K L m) (ℓ ^ k) 𝔣 :=
    isAdmissibleModulusOfDegree_layer K L _ (isAdmissibleModulusOfDegree_of_dvd K L hn hk hadm)
  obtain ⟨hontoM, hkerM⟩ :=
    LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_isAdmissibleModulusOfDegree
      K (layerField K L m) ℓ k hℓ hexpM 𝔣 hadmM
  have hresx : ∀ x, AlgEquiv.restrictNormalHom (layerField K L m) (artinSymbol K L 𝔣 x) =
      artinSymbol K (layerField K L m) 𝔣 x :=
    restrictNormalHom_artinSymbol K L _ hadmM
  refine ⟨fun x hx => ?_, fun g => ?_⟩
  · rw [← hres, hresx, ← MonoidHom.mem_ker, hkerM, normRaySubgroup]
    exact Subgroup.mem_sup_left hx
  · obtain ⟨x, hx⟩ := hontoM (AlgEquiv.restrictNormalHom (layerField K L m) g)
    rw [← hresx] at hx
    have h1 : (g * (artinSymbol K L 𝔣 x)⁻¹) ^ m = 1 := by
      rw [← hres, map_mul, map_inv, hx, mul_inv_cancel]
    rw [mul_pow, inv_pow, mul_inv_eq_one] at h1
    rw [h1]
    exact ⟨x ^ m, map_pow _ _ _⟩

private theorem artinLaw_of_pow_eq_one (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (n : ℕ) (hn : n ≠ 0)
    (hexp : ∀ x : L ≃ₐ[K] L, x ^ n = 1) (𝔣 : Ideal (𝓞 K))
    (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree K L n 𝔣) :
    Function.Surjective (artinSymbol K L 𝔣) ∧ (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  have hlayer : ∀ ℓ ∈ n.primeFactors,
      (∀ x : ↥(coprimeToModulus K 𝔣), x ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) →
          artinSymbol K L 𝔣 x ^ (n / ℓ ^ n.factorization ℓ) = 1) ∧
        ∀ g : L ≃ₐ[K] L, g ^ (n / ℓ ^ n.factorization ℓ) ∈ (artinSymbol K L 𝔣).range := fun ℓ hℓ =>
    pow_artinSymbol_eq_one_of_mem_ray_and_pow_mem_range K L 𝔣 hn hadm ℓ (n.factorization ℓ) _
      (Nat.prime_of_mem_primeFactors hℓ) (Nat.ordProj_dvd n ℓ)
      fun g => by rw [← pow_mul, Nat.ordProj_mul_ordCompl_eq_self, hexp]
  have honto : Function.Surjective (artinSymbol K L 𝔣) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro g _
    rw [← QuotientGroup.eq_one_iff]
    refine eq_one_of_pow_eq_one_of_forall_pow_ordCompl_eq_one hn ?_ fun ℓ hℓ => ?_
    · rw [← QuotientGroup.mk_pow, hexp, QuotientGroup.mk_one]
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact (hlayer ℓ hℓ).2 g
  have hle : normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker := by
    rw [normRaySubgroup]
    refine sup_le (fun x hx => ?_) (relNormCTM_range_le_ker_artinSymbol K L 𝔣 fun w hw =>
      artinFrob_placeUnder_pow_inertiaDeg_eq_one K L w (inertia_eq_bot_of_isAdmissibleModulusOfDegree K L hadm _ hw))
    rw [MonoidHom.mem_ker]
    exact eq_one_of_pow_eq_one_of_forall_pow_ordCompl_eq_one hn (hexp _) fun ℓ hℓ => (hlayer ℓ hℓ).1 x hx
  exact ⟨honto, ker_eq_of_le_of_surjective_of_index_dvd _ _ hle honto (secondInequalityCTM_pair K L 𝔣)⟩

end Layers
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"

set_option autoImplicit false
p2m_open "NumberField NumberField.NormIndex LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree.LanglandsTunnell.P2.Artin"
universe u v

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (n : ℕ) (hn : n ≠ 0) (hexp : ∀ x : L ≃ₐ[K] L, x ^ n = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulusOfDegree K L n 𝔣) :
    Function.Surjective (artinSymbol K L 𝔣) ∧ (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  exact LanglandsTunnell.P2.Artin.artinLaw_of_pow_eq_one K L n hn hexp 𝔣 hadm

end S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
end P2MW
export P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree (solution)
