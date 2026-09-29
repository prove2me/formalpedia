-- Prove2me | solution 1 for LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6af326d9-ae8f-50fe-8b9f-3068aa92132a

import Theorems.Thm_LanglandsTunnell_Artin_exists_artinFieldCore_nonempty_artinPairCore
import Theorems.Thm_LanglandsTunnell_Artin_exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore
import Theorems.Thm_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one
import Theorems.Thm_LanglandsTunnell_P2_Artin_normRaySubgroup_index_eq_of_anchors
import Theorems.Thm_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic
import Theorems.Thm_M4aKummer_normClassIndex_dvd_card_aut_of_isSolvable
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply"
p2m_attr_erase "simp" "Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

namespace Deep
namespace NTSupply
p2m_export "Deep.NTSupply" "coprimeToModulus narrowRaySubgroup raySymbol hasFiniteMulSupport_raySymbol_factors raySymbolUnitsHom raySymbolHom raySymbolHom_apply finite primeUnit primeUnit_val primeUnit_mem_coprimeToModulus raySymbol_primeUnit"
p2m_open "Deep.NTSupply Deep"
end Deep.NTSupply

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"
end HeckeCharacter

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P0
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P5
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P5

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
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

private theorem pow_smul_sub_pow_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (k : ℕ) (x : S) :
    σ ^ k • x - x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hσQ : ∀ y ∈ Q, σ • y ∈ Q := fun y hy => by
      have hstab := H.mem_stabilizer
      rw [MulAction.mem_stabilizer_iff] at hstab
      have h := Ideal.smul_mem_pointwise_smul σ y Q hy
      rwa [hstab] at h
    have h1 : σ ^ (k + 1) • x - σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
      rw [pow_succ', mul_smul, ← smul_sub]
      exact hσQ _ (ih x)
    have h2 : σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) - x ^ (Nat.card (R ⧸ Q.under R) ^ (k + 1)) ∈ Q := by
      rw [smul_pow', pow_succ', pow_mul]
      exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ _) (H x)
    have h := Q.add_mem h1 h2
    rwa [sub_add_sub_cancel] at h

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open NumberField IsDedekindDomain

open scoped Pointwise

section FrobLike

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

private theorem mul_inv_mem_inertia_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) : σ * τ⁻¹ ∈ Q.inertia G := by
  intro x
  have h1 := hσ (τ⁻¹ • x)
  have h2 := hτ (τ⁻¹ • x)
  rw [smul_inv_smul] at h2
  have h := Q.sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right, ← mul_smul] at h

private theorem eq_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) (hI : Q.inertia G = ⊥) : σ = τ := by
  have h := mul_inv_mem_inertia_of_frobLike hσ hτ
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

end FrobLike
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section ResidueTower

attribute [local instance] Ideal.Quotient.field

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem natCard_residue_eq_pow (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  rw [Ideal.inertiaDeg_algebraMap]
  exact Module.natCard_eq_pow_finrank

end ResidueTower
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Norm

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

private theorem restrictNormal_artinFrob_eq_pow [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    ((artinFrob E N w).restrictScalars K).restrictNormal M = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI : ((primeAbove E N w).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove E N w)
  have hQMv : ((primeAbove E N w).under (𝓞 M)).under (𝓞 K) = v.asIdeal := by
    rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), under_primeAbove, hwv]
  haveI : Finite (𝓞 M ⧸ (primeAbove E N w).under (𝓞 M)) := finite_quotient_of_under_eq K M v hQMv

  have hw : Nat.card (𝓞 E ⧸ (primeAbove E N w).under (𝓞 E)) = Nat.card (𝓞 E ⧸ w.asIdeal) := by rw [under_primeAbove]
  have hφ : ∀ y : 𝓞 M, (((artinFrob E N w).restrictScalars K).restrictNormal M) • y - y ^ Nat.card (𝓞 E ⧸ w.asIdeal)
      ∈ (primeAbove E N w).under (𝓞 M) := by
    intro y
    have hkey : algebraMap (𝓞 M) (𝓞 N) ((((artinFrob E N w).restrictScalars K).restrictNormal M) • y)
        = (artinFrob E N w) • algebraMap (𝓞 M) (𝓞 N) y := by
      refine RingOfIntegers.ext ?_
      show algebraMap M N ((((artinFrob E N w).restrictScalars K).restrictNormal M) (y : M)) = (artinFrob E N w) (algebraMap M N (y : M))
      exact AlgEquiv.restrictNormal_commutes _ M (y : M)
    rw [Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    erw [hkey]
    rw [← hw]
    exact isArithFrobAt_artinFrob E N w (algebraMap (𝓞 M) (𝓞 N) y)

  have hF : IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M))) ((primeAbove E N w).under (𝓞 M)) :=
    IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) _
  have hcard : Nat.card (𝓞 E ⧸ w.asIdeal)
      = Nat.card (𝓞 K ⧸ ((primeAbove E N w).under (𝓞 M)).under (𝓞 K)) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [hQMv]
    exact natCard_residue_eq_pow v w hwv
  have hFf : ∀ y : 𝓞 M, arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M)) ^ v.asIdeal.inertiaDeg' w.asIdeal • y
      - y ^ Nat.card (𝓞 E ⧸ w.asIdeal) ∈ (primeAbove E N w).under (𝓞 M) := fun y => by
    rw [hcard]
    exact pow_smul_sub_pow_mem hF _ y

  rw [eq_of_frobLike hφ hFf hI, arithFrobAt_eq_artinFrob K M v ((primeAbove E N w).under (𝓞 M)) hQMv hI]

end Norm
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply"

open scoped IsMulCommutative nonZeroDivisors

section Finite

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem resHom_artinFrob (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal :=
  restrictNormal_artinFrob_eq_pow K M E N v w hwv hI

variable [IsMulCommutative (N ≃ₐ[E] N)]

end Tower
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM ideleFirstIneqDataAt_of_isCyclic"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

set_option maxHeartbeats 3200000

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff relNormCTM ideleFirstIneqDataAt_of_isCyclic"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {I : Type*} [CommGroup I] (𝔑 : Subgroup I) {G : Type*} [Group G] (ω : I →* G) (σ : G)

section Transfer

variable {Ip : Type*} [CommGroup Ip] (N : Ip →* I) (ωp : Ip →* G)

private def transferClass (b : Ip) : I ⧸ 𝔑 := ((N b : I) : I ⧸ 𝔑)

variable {𝔑 N ωp σ}

private theorem transferClass_indep (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b b' : Ip} (hb : ωp b = σ) (hb' : ωp b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N b' := by
  unfold transferClass
  rw [QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, hb, hb', inv_mul_cancel])

private theorem transferClass_pow_orderOf (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) :
    transferClass 𝔑 N b ^ orderOf σ = 1 := by
  unfold transferClass
  rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff]
  exact hker _ (by rw [map_pow, hb, pow_orderOf_eq_one])

private theorem coe_eq_transferClass_zpow (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) {P : Ip} {p : I} (hNP : N P = p)
    {d : ℤ} (hd : ωp P = σ ^ d) : ((p : I) : I ⧸ 𝔑) = transferClass 𝔑 N b ^ d := by
  unfold transferClass
  rw [← hNP, ← QuotientGroup.mk_zpow, ← map_zpow, QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, map_zpow, hb, hd, inv_mul_cancel])

private theorem apply_eq_zpow_of_transfer (hcompat : ∀ x, ω (N x) = ωp x) {P : Ip} {p : I} (hNP : N P = p) {d : ℤ} (hd : ωp P = σ ^ d) :
    ω p = σ ^ d := by
  rw [← hNP, hcompat, hd]

end Transfer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Crossing

variable {Ip Iq Ipq : Type*} [CommGroup Ip] [CommGroup Iq] [CommGroup Ipq]

variable {N : Ip →* I} {ωp : Ip →* G} {N' : Iq →* I} {ωq : Iq →* G}

variable {𝔑 σ}

private theorem transferClass_eq_of_common_norm (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    {bp : Ip} {bq : Iq} (hN : N bp = N' bq) (hbp : ωp bp = σ) (hbq : ωq bq = σ)
    {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) : transferClass 𝔑 N b = transferClass 𝔑 N' b' := by
  rw [transferClass_indep hkerp hb hbp, transferClass_indep hkerq hb' hbq]
  unfold transferClass
  rw [hN]

variable {Np : Ipq →* Ip} {Nq : Ipq →* Iq} {ωpq : Ipq →* G}

end Crossing
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

private theorem exists_zpow_of_mem_closure (c : I ⧸ 𝔑) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) :
    ∃ e : ℤ, ω x = σ ^ e ∧ ((x : I) : I ⧸ 𝔑) = c ^ e := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => exact ⟨0, by rw [map_one, zpow_zero], by rw [QuotientGroup.mk_one, zpow_zero]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨e, he, he'⟩ := ihy
    obtain ⟨f, hf, hf'⟩ := ihz
    exact ⟨e + f, by rw [map_mul, he, hf, zpow_add], by rw [QuotientGroup.mk_mul, he', hf', zpow_add]⟩
  | inv y _ ihy =>
    obtain ⟨e, he, he'⟩ := ihy
    exact ⟨-e, by rw [map_inv, he, zpow_neg], by rw [QuotientGroup.mk_inv, he', zpow_neg]⟩

private theorem mem_of_ker_of_classes (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) (hω : ω x = 1) :
    x ∈ 𝔑 := by
  obtain ⟨e, he, he'⟩ := exists_zpow_of_mem_closure 𝔑 ω σ c S hS hx

  have hdvd : (orderOf σ : ℤ) ∣ e := orderOf_dvd_iff_zpow_eq_one.mpr (by rw [← he, hω])
  have hce : c ^ e = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    rw [zpow_mul, zpow_natCast, hc, one_zpow]
  rw [← QuotientGroup.eq_one_iff, he', hce]

private theorem ker_inf_closure_le (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) : ω.ker ⊓ Subgroup.closure S ≤ 𝔑 :=
  fun _ hx => mem_of_ker_of_classes 𝔑 ω σ c hc S hS hx.2 (MonoidHom.mem_ker.mp hx.1)

private theorem ker_inf_closure_le_of_transfer {Ip : Type*} [CommGroup Ip] (S : Set I)
    (N : I → (Ip →* I)) (ωp : I → (Ip →* G)) (P : I → Ip) (d : I → ℤ)
    (hcompat : ∀ p ∈ S, ∀ x, ω (N p x) = ωp p x) (hker : ∀ p ∈ S, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ S, N p (P p) = p) (hd : ∀ p ∈ S, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ S, ∀ q ∈ S, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) :
    ω.ker ⊓ Subgroup.closure S ≤ 𝔑 := by
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    obtain ⟨b₀, -, -, hb₀⟩ := hcross p₀ hp₀ p₀ hp₀
    refine ker_inf_closure_le 𝔑 ω σ (transferClass 𝔑 (N p₀) b₀) (transferClass_pow_orderOf (hker p₀ hp₀) hb₀) S ?_
    intro p hp
    obtain ⟨bp, bq, hN, hbp⟩ := hcross p₀ hp₀ p hp

    have hbq : ωp p bq = σ := by rw [← hcompat p hp, ← hN, hcompat p₀ hp₀, hbp]
    refine ⟨d p, apply_eq_zpow_of_transfer ω (hcompat p hp) (hNP p hp) (hd p hp), ?_⟩
    rw [transferClass_eq_of_common_norm (hker p₀ hp₀) (hker p hp) hN hbp hbq hb₀ hbq]
    exact coe_eq_transferClass_zpow (hker p hp) hbq (hNP p hp) (hd p hp)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Subgroup.closure_empty, inf_bot_eq]
    exact bot_le

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
namespace Count
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {A T : Type*} [Group A] [Group T]

private theorem ker_eq_and_surjective_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) :
    φ.ker = N ∧ Function.Surjective φ := by
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hkidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hle : Nat.card φ.range ≤ Nat.card T :=
    Nat.card_le_card_of_injective _ φ.range.subtype_injective
  have hmul := Subgroup.relIndex_mul_index hker
  rw [hkidx, hidx] at hmul

  have hrpos : 0 < Nat.card φ.range := Nat.card_pos
  have hrel1 : φ.ker.relIndex N = 1 := by
    have h1 : φ.ker.relIndex N * Nat.card T ≤ 1 * Nat.card T := by rw [one_mul, hmul]; exact hle
    have h2 : 1 ≤ φ.ker.relIndex N := by
      rcases Nat.eq_zero_or_pos (φ.ker.relIndex N) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hTpos) h2
  have hkerN : φ.ker = N := le_antisymm hker (Subgroup.relIndex_eq_one.mp hrel1)
  refine ⟨hkerN, ?_⟩

  have hcard : Nat.card φ.range = Nat.card T := by
    rw [← hkidx, hkerN, hidx]
  have : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by simpa using hcard)
  exact MonoidHom.range_eq_top.mp this

end LanglandsTunnell.P2.Artin.Count
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

variable (𝔣 : Ideal (𝓞 K)) (𝔑 : Subgroup ↥(coprimeToModulus K 𝔣)) (σ : L ≃ₐ[K] L)

variable {Ip : Type*} [CommGroup Ip]
  (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣))) (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
  (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)

private theorem artinSymbol_ker_eq_and_surjective_of_transfer
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L)) :
    (artinSymbol K L 𝔣).ker = 𝔑 ∧ Function.Surjective (artinSymbol K L 𝔣) := by
  refine Count.ker_eq_and_surjective_of_le_of_index_eq_card (artinSymbol K L 𝔣) ?_ hidx
  have h := ker_inf_closure_le_of_transfer 𝔑 (artinSymbol K L 𝔣) σ (primeCarriers K 𝔣) N ωp P d hcompat hker hNP hd hcross
  rwa [closure_primeCarriers_eq_top, inf_top_eq] at h

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section hcompat

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_relNormCTM_primeCarrier (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    artinSymbol K M 𝔣 (relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
      = resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩) := by
  have heq : placeUnder' K E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  have hvcop : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := heq ▸ hv

  rw [show relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = (⟨primeUnit K (placeUnder' K E w), primeUnit_mem_coprimeToModulus K hvcop⟩
          : ↥(coprimeToModulus K 𝔣)) ^ ((placeUnder' K E w).asIdeal.inertiaDeg' w.asIdeal) from
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact relNormCTM_primeUnit K E hw),
    map_pow, artinSymbol_prime K M hvcop]

  rw [artinSymbol_prime E N hw, resHom_artinFrob K M E N v w hwv hI, heq]

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_comp_relNormCTM_eq (𝔣 : Ideal (𝓞 K))
    (hI_all : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ modulusExt K E 𝔣 →
      ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    (artinSymbol K M 𝔣).comp (relNormCTM K E 𝔣)
      = (resHom K M E N).comp (artinSymbol E N (modulusExt K E 𝔣)) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E (modulusExt K E 𝔣)) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K E 𝔣 w).mp h)
  exact artinSymbol_relNormCTM_primeCarrier K M E N 𝔣 hw hv (placeUnder'_asIdeal K E w).symm
    (hI_all w hw)

end hcompat
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem index_normRaySubgroup_eq_card (𝔣 : Ideal (𝓞 K))
    (hCSb : SecondInequalityCTM K L 𝔣) (hCSc1 : FirstInequalityCTM K L 𝔣) :
    (normRaySubgroup K L 𝔣).index = Nat.card (L ≃ₐ[K] L) :=
  Nat.dvd_antisymm hCSb hCSc1

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply"

open scoped nonZeroDivisors IsMulCommutative

section Family

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

variable (𝔣 : Ideal (𝓞 K)) (𝔑 : Subgroup ↥(coprimeToModulus K 𝔣)) (σ : L ≃ₐ[K] L)

variable {Ip : ↥(primeCarriers K 𝔣) → Type*} [∀ i, CommGroup (Ip i)]
  (N : ∀ i, Ip i →* ↥(coprimeToModulus K 𝔣)) (ωp : ∀ i, Ip i →* (L ≃ₐ[K] L)) (P : ∀ i, Ip i)
  (d : ↥(primeCarriers K 𝔣) → ℤ)

private theorem artinSymbol_ker_eq_and_surjective_of_family
    (hcompat : ∀ i x, artinSymbol K L 𝔣 (N i x) = ωp i x)
    (hker : ∀ i x, ωp i x = 1 → N i x ∈ 𝔑)
    (hNP : ∀ i, N i (P i) = (i : ↥(coprimeToModulus K 𝔣))) (hd : ∀ i, ωp i (P i) = σ ^ d i)
    (hcross : ∀ i j, ∃ (b : Ip i) (b' : Ip j), N i b = N j b' ∧ ωp i b = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L)) :
    (artinSymbol K L 𝔣).ker = 𝔑 ∧ Function.Surjective (artinSymbol K L 𝔣) := by
  classical

  let N' : ↥(coprimeToModulus K 𝔣) → ((∀ i, Ip i) →* ↥(coprimeToModulus K 𝔣)) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then (N ⟨p, hp⟩).comp (Pi.evalMonoidHom Ip ⟨p, hp⟩) else 1
  let ω' : ↥(coprimeToModulus K 𝔣) → ((∀ i, Ip i) →* (L ≃ₐ[K] L)) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then (ωp ⟨p, hp⟩).comp (Pi.evalMonoidHom Ip ⟨p, hp⟩) else 1
  let P' : ↥(coprimeToModulus K 𝔣) → (∀ i, Ip i) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then Pi.mulSingle (⟨p, hp⟩ : ↥(primeCarriers K 𝔣)) (P ⟨p, hp⟩) else 1
  let d' : ↥(coprimeToModulus K 𝔣) → ℤ := fun p => if hp : p ∈ primeCarriers K 𝔣 then d ⟨p, hp⟩ else 0
  refine artinSymbol_ker_eq_and_surjective_of_transfer K L 𝔣 𝔑 σ N' ω' P' d' ?_ ?_ ?_ ?_ ?_ hidx
  · intro p hp x
    simp only [N', ω', dif_pos hp, MonoidHom.comp_apply]
    exact hcompat _ _
  · intro p hp x hx
    simp only [N', ω', dif_pos hp, MonoidHom.comp_apply] at hx ⊢
    exact hker _ _ hx
  · intro p hp
    simp only [N', P', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
    exact hNP _
  · intro p hp
    simp only [ω', P', d', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
    exact hd _
  · intro p hp q hq
    obtain ⟨b, b', hN, hω⟩ := hcross ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨Pi.mulSingle (⟨p, hp⟩ : ↥(primeCarriers K 𝔣)) b, Pi.mulSingle (⟨q, hq⟩ : ↥(primeCarriers K 𝔣)) b', ?_, ?_⟩
    · simp only [N', dif_pos hp, dif_pos hq, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
      exact hN
    · simp only [ω', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
      exact hω

end Family
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

omit [NumberField K] [IsGalois K L] in

private theorem admissibleExp_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < admissibleExp K v := Nat.succ_pos _

omit [NumberField L] [IsGalois K L] in

private theorem dvd_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) : v.asIdeal ∣ 𝔣 :=
  dvd_trans (dvd_pow_self _ (admissibleExp_pos K v).ne') (h.2 v hv)

omit [NumberField L] [IsGalois K L] in

private theorem inertia_eq_bot_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ 𝔣) : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥ :=
  not_ne_iff.mp fun hne => hv (dvd_of_isAdmissibleModulus K L h hne)

end Admissible
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Hfrob

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

section

set_option autoImplicit false

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hd

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

set_option maxSynthPendingDepth 3 in

private theorem resHom_artinSymbol_primeCarrier_eq_artinFrob (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
      = artinFrob K M v := by
  have hcompat := artinSymbol_relNormCTM_primeCarrier K M E N 𝔣 hw hv hwv hI
  rw [relNormCTM_primeCarrier_of_inertiaDeg_eq_one K E hw hv hwv hf, artinSymbol_prime K M hv] at hcompat
  exact hcompat.symm

end hd
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

section

set_option autoImplicit false

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Carrier

variable (K : Type*) [Field K] [NumberField K]

@[scoped simp] private theorem coe_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    ((ctmInclusion K h x : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = (x : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := rfl

private theorem ctmInclusion_primeCarrier {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪) :
    ctmInclusion K h (primeCarrier K 𝔪 v hv) = primeCarrier K 𝔣 v (fun hv' => hv (dvd_trans hv' h)) := rfl

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Symbol

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem artinSymbol_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    artinSymbol K M 𝔣 (ctmInclusion K h x) = artinSymbol K M 𝔪 x := by
  show raySymbolHom K 𝔣 (artinFrob K M) _ = raySymbolHom K 𝔪 (artinFrob K M) _
  rw [raySymbolHom_apply, raySymbolHom_apply, coe_ctmInclusion]

end Symbol
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter"

section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
  (c : ArtinFieldCore K L 𝔣 i)

private theorem hcompat_of_core (x : c.Ip) : artinSymbol K L 𝔣 (c.Ni x) = c.ωpi x := by
  show artinSymbol K L 𝔣 (ctmInclusion K c.h𝔪 (relNormCTM K c.E c.𝔪 x)) = _
  rw [artinSymbol_ctmInclusion K L c.h𝔪]
  exact DFunLike.congr_fun (artinSymbol_comp_relNormCTM_eq K L c.E c.N c.𝔪 c.hI_E) x

private theorem hNP_of_core : c.Ni c.Pi = (i : ↥(coprimeToModulus K 𝔣)) := by
  show ctmInclusion K c.h𝔪
      (relNormCTM K c.E c.𝔪 ⟨primeUnit c.E c.w, primeUnit_mem_coprimeToModulus c.E c.hw⟩) = _
  rw [relNormCTM_primeCarrier_of_inertiaDeg_eq_one K c.E c.hw c.hv𝔪 c.hwv c.hf]
  exact (ctmInclusion_primeCarrier K c.h𝔪 c.v c.hv𝔪).trans c.hvi

private theorem hd_of_core : c.ωpi c.Pi = artinFrob K L c.v :=
  resHom_artinSymbol_primeCarrier_eq_artinFrob K L c.E c.N c.𝔪 c.hw c.hv𝔪 c.hwv c.hf (c.hI_E c.w c.hw)

private theorem hd_zpow_of_core {σ : L ≃ₐ[K] L} (hσ : ∀ g : L ≃ₐ[K] L, g ∈ Subgroup.zpowers σ) :
    c.ωpi c.Pi = σ ^ (Subgroup.mem_zpowers_iff.mp (hσ (artinFrob K L c.v))).choose :=
  (hd_of_core c).trans (Subgroup.mem_zpowers_iff.mp (hσ (artinFrob K L c.v))).choose_spec.symm

end PerICore
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.Deep.NTSupply NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one P2.Artin.normRaySubgroup_index_eq_of_anchors"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup_index_eq_of_anchors"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime normRaySubgroup_index_eq_of_anchors"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.HeckeCharacter IntermediateField"

attribute [local instance] Ideal.Quotient.field

section AdmLayer

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

private theorem inertia_ne_bot_iff_ramificationIdxIn_ne_one (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K M v).inertia (M ≃ₐ[K] M) ≠ ⊥ ↔ v.asIdeal.ramificationIdxIn (𝓞 M) ≠ 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal (primeAbove K M v), ne_eq, ne_eq,
    Subgroup.card_eq_one]

private theorem inertia_eq_bot_of_isAdmissibleModulus_of_not_under_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K M 𝔣)
    (P : Ideal (𝓞 M)) [hPm : P.IsMaximal] (hP : ¬ P.under (𝓞 K) ∣ 𝔣) : P.inertia (M ≃ₐ[K] M) = ⊥ := by
  have hPne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField M)
  let p₀ : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), (hPm.under (𝓞 K)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (hPm.under (𝓞 K)) (RingOfIntegers.not_isField K)⟩
  have hI0 : (primeAbove K M p₀).inertia (M ≃ₐ[K] M) = ⊥ := inertia_eq_bot_of_isAdmissibleModulus K M h𝔣 p₀ hP
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

private theorem isAdmissibleModulus_layer {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K M 𝔣) : IsAdmissibleModulus K F 𝔣 := by
  haveI := isGalois_layer K M F
  refine ⟨h.1, fun v hv => h.2 v ?_⟩
  rw [inertia_ne_bot_iff_ramificationIdxIn_ne_one] at hv ⊢
  exact ramificationIdxIn_ne_one_of_layer K M F v hv

omit [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem finrank_layer_dvd : Module.finrank K F ∣ Module.finrank K M :=
  ⟨Module.finrank F M, (Module.finrank_mul_finrank K F M).symm⟩

end AdmLayer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section Restrict

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] (M : IntermediateField K L)

private theorem restrictNormalHom_artinSymbol [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hadmM : IsAdmissibleModulus K M 𝔣) (x : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K L 𝔣 x) = artinSymbol K M 𝔣 x := by
  suffices h : (AlgEquiv.restrictNormalHom M).comp (artinSymbol K L 𝔣) = artinSymbol K M 𝔣 from DFunLike.congr_fun h x
  refine MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top K 𝔣) ?_
  rintro _ ⟨v, hv, rfl⟩
  show AlgEquiv.restrictNormalHom M (artinSymbol K L 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩)
    = artinSymbol K M 𝔣 ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩
  rw [artinSymbol_prime K L hv, artinSymbol_prime K M hv]
  refine restrictNormal_artinFrob K M L v ?_
  haveI : ((primeAbove K L v).under (𝓞 M)).IsMaximal := (primeAbove_isMaximal K L v).under (𝓞 M)
  refine inertia_eq_bot_of_isAdmissibleModulus_of_not_under_dvd K M hadmM _ ?_
  rw [Ideal.under_under, under_primeAbove]
  exact hv

end Restrict
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section CyclicCard

variable {G : Type*} [Group G] [IsCyclic G]

private theorem card_dvd_of_isCyclic_of_pow_eq_one {ℓ k : ℕ} (hexp : ∀ x : G, x ^ (ℓ ^ k) = 1) (hk : ℓ ^ k ∣ 24) :
    Nat.card G ∣ 24 := by
  have h := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rw [IsCyclic.exponent_eq_card] at h
  exact h.trans hk

end CyclicCard
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

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

private theorem firstInequalityCTM_pair [IsCyclic (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (hadm : IsAdmissibleModulus K M 𝔣)
    (h24 : Module.finrank K M ∣ 24) : FirstInequalityCTM K M 𝔣 := by
  obtain ⟨Nrm, hA1, hA2, hA3, h4⟩ := HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic K M h24 𝔣
  unfold FirstInequalityCTM
  rw [LanglandsTunnell.P2.Artin.normRaySubgroup_index_eq_of_anchors K M 𝔣 hadm.1 Nrm hA1 hA2 (hA3 hadm),
    IsGalois.card_aut_eq_finrank]
  exact h4

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem data_and_firstInequalityCTM_of_prime_layer {G : Type*} [Group G] (hG : Nat.card G ∣ 24) (f : (M ≃ₐ[K] M) →* G)
    (hf : Function.Injective f) (F : IntermediateField K M) (hF : (Module.finrank K F).Prime) (𝔪 : Ideal (𝓞 K))
    (hadm : IsAdmissibleModulus K M 𝔪) :
    IdeleFirstIneqDataAt K F 𝔪 ∧ FirstInequalityCTM K F 𝔪 := by
  haveI := isGalois_layer K M F
  haveI := isMulCommutative_gal_layer K M F
  haveI : Fact (Module.finrank K F).Prime := ⟨hF⟩
  haveI : IsCyclic (F ≃ₐ[K] F) := isCyclic_of_prime_card (p := Module.finrank K F) (IsGalois.card_aut_eq_finrank K F)
  have h24 : Module.finrank K F ∣ 24 := by
    refine (finrank_layer_dvd K M F).trans ?_
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Subgroup.card_dvd_of_injective f hf).trans hG
  exact ⟨HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic K F h24 𝔪, firstInequalityCTM_pair K F (isAdmissibleModulus_layer K M F hadm) h24⟩

end Inequalities
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section CyclicLaw

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

private theorem artinLaw_of_isCyclic [IsCyclic (L ≃ₐ[K] L)] (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) (hk : ℓ ^ k ∣ 24) :
    (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 ∧ Function.Surjective (artinSymbol K L 𝔣) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨D, hP⟩ := LanglandsTunnell.Artin.exists_artinFieldCore_nonempty_artinPairCore K L ℓ k hℓ hexp 𝔣 hadm σ
  let P : ∀ i j : ↥(primeCarriers K 𝔣), ArtinPairCore K L 𝔣 σ (D i) (D j) := fun i j => (hP i j).some
  have hcardL : Nat.card (L ≃ₐ[K] L) ∣ 24 := card_dvd_of_isCyclic_of_pow_eq_one hexp hk
  have hCSb_i : ∀ i, SecondInequalityCTM (D i).E (D i).N (modulusExt K (D i).E (D i).𝔪) := fun i =>
    secondInequalityCTM_pair (D i).E (D i).N _
  have hFI_i : ∀ i, ∀ F : IntermediateField (D i).E (D i).N, (Module.finrank (D i).E F).Prime →
      FirstInequalityCTM (D i).E F (modulusExt K (D i).E (D i).𝔪) := fun i F hF =>
    (data_and_firstInequalityCTM_of_prime_layer (D i).E (D i).N hcardL (resHom K L (D i).E (D i).N) (D i).hresInj F hF _
      (D i).hadm).2
  have hdata_ij : ∀ i j, ∀ F : IntermediateField (P i j).E'' (P i j).N'', (Module.finrank (P i j).E'' F).Prime →
      IdeleFirstIneqData (P i j).E'' (P i j).N'' F (modulusExt K (P i j).E'' (P i j).𝔪'') := fun i j F hF =>
    (data_and_firstInequalityCTM_of_prime_layer (P i j).E'' (P i j).N'' hcardL (resHom K L (P i j).E'' (P i j).N'')
      (P i j).hresInj'' F hF _ (P i j).hadm'').1
  have hcross := LanglandsTunnell.Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore D P hdata_ij
  have hCSb : SecondInequalityCTM K L 𝔣 := secondInequalityCTM_pair K L 𝔣
  have h24 : Module.finrank K L ∣ 24 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hcardL
  have hCSc1 : FirstInequalityCTM K L 𝔣 := firstInequalityCTM_pair K L hadm h24
  exact artinSymbol_ker_eq_and_surjective_of_family K L 𝔣 (normRaySubgroup K L 𝔣) σ
    (fun i => (D i).Ni) (fun i => (D i).ωpi) (fun i => (D i).Pi)
    (fun i => (Subgroup.mem_zpowers_iff.mp (hσ (artinFrob K L (D i).v))).choose)
    (fun i x => hcompat_of_core (D i) x)
    (fun i x hx => LanglandsTunnell.Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one (D i) (hCSb_i i) (hFI_i i) x hx)
    (fun i => hNP_of_core (D i)) (fun i => hd_zpow_of_core (D i) hσ) hcross
    (index_normRaySubgroup_eq_card K L 𝔣 hCSb hCSc1)

end CyclicLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

section AbelianLaw

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

private theorem layer_of_cyclic_quotient {C : Type*} [Group C] [IsCyclic C] (χ : (L ≃ₐ[K] L) →* C)
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) (hk : ℓ ^ k ∣ 24) :
    (∀ x : ↥(coprimeToModulus K 𝔣), x ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) → χ (artinSymbol K L 𝔣 x) = 1) ∧
    ((∀ x : ↥(coprimeToModulus K 𝔣), χ (artinSymbol K L 𝔣 x) = 1) → ∀ g : L ≃ₐ[K] L, χ g = 1) := by
  haveI hGal : IsGalois K (fixedField χ.ker) := isGalois_layer K L _
  haveI hComm : IsMulCommutative (fixedField χ.ker ≃ₐ[K] fixedField χ.ker) := isMulCommutative_gal_layer K L _
  haveI : IsCyclic ((L ≃ₐ[K] L) ⧸ χ.ker) :=
    isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange χ).symm.toMonoidHom (QuotientGroup.quotientKerEquivRange χ).symm.surjective
  haveI : IsCyclic (fixedField χ.ker ≃ₐ[K] fixedField χ.ker) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient χ.ker).toMonoidHom (IsGalois.normalAutEquivQuotient χ.ker).surjective
  have hres_iff : ∀ g : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom (fixedField χ.ker) g = 1 ↔ χ g = 1 := fun g => by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField, MonoidHom.mem_ker]
  have hexpM : ∀ x : fixedField χ.ker ≃ₐ[K] fixedField χ.ker, x ^ (ℓ ^ k) = 1 := fun x => by
    obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L x
    rw [← map_pow, hexp, map_one]
  have hadmM : IsAdmissibleModulus K (fixedField χ.ker) 𝔣 := isAdmissibleModulus_layer K L _ hadm
  obtain ⟨hkerM, hontoM⟩ := artinLaw_of_isCyclic K (fixedField χ.ker) ℓ k hℓ hexpM 𝔣 hadmM hk
  have hresx : ∀ x, AlgEquiv.restrictNormalHom (fixedField χ.ker) (artinSymbol K L 𝔣 x) = artinSymbol K (fixedField χ.ker) 𝔣 x :=
    restrictNormalHom_artinSymbol K L _ hadmM
  refine ⟨fun x hx => ?_, fun htriv g => ?_⟩
  · rw [← hres_iff, hresx, ← MonoidHom.mem_ker, hkerM, normRaySubgroup]
    exact Subgroup.mem_sup_left hx
  · obtain ⟨x, hx⟩ := hontoM (AlgEquiv.restrictNormalHom (fixedField χ.ker) g)
    rw [← hresx] at hx
    have h1 : χ ((artinSymbol K L 𝔣 x)⁻¹ * g) = 1 := by
      rw [← hres_iff, map_mul, map_inv, hx, inv_mul_cancel]
    rwa [map_mul, map_inv, htriv x, inv_one, one_mul] at h1

private theorem artinLaw (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) (hk : ℓ ^ k ∣ 24) :
    Function.Surjective (artinSymbol K L 𝔣) ∧ (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  have honto : Function.Surjective (artinSymbol K L 𝔣) := by
    rw [← MonoidHom.range_eq_top]
    by_contra hne
    obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite ((L ≃ₐ[K] L) ⧸ (artinSymbol K L 𝔣).range)
    have hg1 : e (QuotientGroup.mk' (artinSymbol K L 𝔣).range g) ≠ 1 := fun h =>
      hg ((QuotientGroup.eq_one_iff g).mp (e.injective (h.trans (map_one e).symm)))
    obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' (artinSymbol K L 𝔣).range g) i ≠ 1 := by
      by_contra hall
      exact hg1 (funext fun i => not_not.mp (not_exists.mp hall i))
    let χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod (n i)) :=
      (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp (e.toMonoidHom.comp (QuotientGroup.mk' (artinSymbol K L 𝔣).range))
    have hχ : ∀ x, χ (artinSymbol K L 𝔣 x) = 1 := fun x => by
      have h1 : QuotientGroup.mk' (artinSymbol K L 𝔣).range (artinSymbol K L 𝔣 x) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
      simp only [χ, MonoidHom.comp_apply, h1, map_one]
    exact hi ((layer_of_cyclic_quotient K L χ ℓ k hℓ hexp 𝔣 hadm hk).2 hχ g)
  have hle : normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker := by
    rw [normRaySubgroup]
    refine sup_le (fun x hx => ?_) (relNormCTM_range_le_ker_artinSymbol K L 𝔣 fun w hw =>
      artinFrob_placeUnder_pow_inertiaDeg_eq_one K L w (inertia_eq_bot_of_isAdmissibleModulus K L hadm _ hw))
    rw [MonoidHom.mem_ker]
    obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite (L ≃ₐ[K] L)
    refine e.injective ((funext fun i => ?_).trans (map_one e).symm)
    exact (layer_of_cyclic_quotient K L ((Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp e.toMonoidHom)
      ℓ k hℓ hexp 𝔣 hadm hk).1 x hx
  exact ⟨honto, ker_eq_of_le_of_surjective_of_index_dvd _ _ hle honto (secondInequalityCTM_pair K L 𝔣)⟩

end AbelianLaw
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"

set_option autoImplicit false
p2m_open "NumberField LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour.LanglandsTunnell.P2.Artin"
universe u v

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (ℓ k : ℕ) (hℓ : ℓ.Prime) (hexp : ∀ x : L ≃ₐ[K] L, x ^ (ℓ ^ k) = 1)
    (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (hk : ℓ ^ k ∣ 24) :
    Function.Surjective (artinSymbol K L 𝔣) ∧ (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  exact LanglandsTunnell.P2.Artin.artinLaw K L ℓ k hℓ hexp 𝔣 hadm hk

end S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour
end P2MW
export P2MW.S_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_dvd_twentyFour (solution)
