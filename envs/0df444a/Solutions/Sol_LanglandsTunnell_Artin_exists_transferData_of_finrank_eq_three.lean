-- Prove2me | solution 1 for LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/cc3103bb-974e-586f-b37e-8dcba5d7ca80

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_HeckeCharacter_FiniteOrder
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_Lift48
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_LanglandsTunnell_C8Character
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Theorems.Thm_LanglandsTunnell_Artin_exists_artinFieldCore_nonempty_artinPairCore
import Theorems.Thm_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one
import Theorems.Thm_LanglandsTunnell_Artin_exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore
import Theorems.Thm_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic
import Theorems.Thm_NumberField_PrimeNormIndex_secondInequalityCTM_of_finrank_eq_three
import Theorems.Thm_M4aKummer_normClassIndex_dvd_card_aut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

namespace Deep
namespace NTSupply
p2m_export "Deep.NTSupply" "coprimeToModulus mem_coprimeToModulus_iff mem_narrowRaySet_iff narrowRaySubgroup count_span_singleton_eq_zero_of_sub_one_mem NarrowRayClassGroup NarrowRayClassGroup.mk raySymbol hasFiniteMulSupport_raySymbol_factors raySymbolUnitsHom raySymbolHom raySymbolHom_apply NarrowRayClassGroup.mk_eq_one_of_mem NarrowRayClassGroup.mk_eq_mk_iff mul_mem_narrowRaySet_of_sameSign principalUnit principalUnit_val movingLemma principalUnit_mem_coprimeToModulus primeUnit primeUnit_val primeUnit_mem_coprimeToModulus primeClass raySymbol_primeUnit raySymbolDescend raySymbolDescend_mk"
p2m_open "Deep.NTSupply Deep"
end Deep.NTSupply

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"
end HeckeCharacter

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P0
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P0

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Ambient
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin.Ambient

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageA

private theorem fadContentHom_apply (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v) :=
  rfl

end StageA

section StageB

private theorem coe_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (placeOrd K u v) := by
  rw [fadContentHom_apply, ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit K v ^ placeOrd K u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

private theorem count_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = placeOrd K u w := by
  rw [coe_fadContentHom]
  exact FractionalIdeal.count_finprod K w (placeOrd K u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K u)

private theorem fadContentHom_mem_coprimeToModulus_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (𝔣 : Ideal (𝓞 K)) :
    fadContentHom K u ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [count_fadContentHom, placeOrd_eq_zero_iff]

private theorem placeOrd_unitEmbedding (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K)) := by
  classical

  have hLHS : placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = -WithZero.log (v.valuation K (α : K)) := by
    unfold placeOrd
    rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
      FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (α : K)]
  rw [hLHS]

  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (M := (𝓞 K)⁰) (S := K) (α : K)
  have hnd' : IsLocalization.mk' K n d = (α : K) := hnd
  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [IsLocalization.mk'_zero] at hnd'; exact α.ne_zero hnd'.symm
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [← hnd', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0,
    ← WithZero.exp_sub, WithZero.log_exp, neg_sub_neg,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0)
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0),
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn0),
    show FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d)⁻¹
        = (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d))⁻¹ by
        rw [← one_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          FractionalIdeal.spanSingleton_one, one_div],
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)]
  ring

private theorem coe_fadContentHom_principal (α : Kˣ) :
    ((fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K) := by
  rw [coe_fadContentHom]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr α.ne_zero)]
  exact finprod_congr fun v => by rw [placeOrd_unitEmbedding]

private theorem fadContentHom_unitEmbedding (α : Kˣ) :
    fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) = toPrincipalIdeal (𝓞 K) K α :=
  Units.ext <| (coe_fadContentHom_principal K α).trans (coe_toPrincipalIdeal α).symm

end StageB

end HeckeCharacter

end

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageC

private theorem projFin_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (u : AdeleRing (𝓞 K) K).2 := rfl

private theorem projFin_principal (α : Kˣ) :
    projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)
      = FiniteAdeleRing.unitEmbedding (𝓞 K) K α := by
  apply Units.ext; rfl

omit [NumberField K] in
omit [NumberField K] in
omit [NumberField K] in

private theorem embedding_of_isReal_placeOf (τ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_placeOf K τ) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, show (placeOf K τ).embedding
      = Complex.ofRealHom.comp τ from
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

private theorem archSign_principal (τ : K →+* ℝ) (α : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) ↔ 0 < τ (α : K) := by
  unfold archSign archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    embedding_of_isReal_placeOf K τ]
  rfl

namespace IsAdjuster p2m_export "HeckeCharacter.IsAdjuster" "mk cong sign" end IsAdjuster
namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.coprime {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 u α) :
    fadContentHom K (projFin K (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹))
      ∈ coprimeToModulus K 𝔣 := by
  rw [fadContentHom_mem_coprimeToModulus_iff]
  intro v hv
  rw [projFin_val]
  exact (h.cong v hv).1

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.coprime"
private theorem isAdjuster_one_one (𝔣 : Ideal (𝓞 K)) : IsAdjuster K 𝔣 1 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    refine ⟨?_, ?_⟩
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
      rw [fad_one_apply]; exact map_one _
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
      rw [fad_one_apply, sub_self, map_zero]; exact zero_le'
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

private abbrev adjFinV (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    (u * (pK K α)⁻¹)⁻¹ * (u * (pK K α')⁻¹) = pK K (α * α'⁻¹) := by
  rw [mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, ← mul_assoc u⁻¹, inv_mul_cancel,
    one_mul]

private theorem adjFinV_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    adjFinV K (u * u') (α * α') v = adjFinV K u α v * adjFinV K u' α' v := by
  unfold adjFinV
  rw [show u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) from by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _]
  exact fad_mul_apply K _ _ v

namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.mul {𝔣 : Ideal (𝓞 K)} {u u' : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u' α') :
    IsAdjuster K 𝔣 (u * u') (α * α') := by
  have hfac : u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) := by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _
  refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
  · show Valued.v (adjFinV K (u * u') (α * α') v) = 1 ∧
      Valued.v (adjFinV K (u * u') (α * α') v - 1) ≤ _
    rw [adjFinV_mul]
    exact unit_cong_mul K (hα.cong v hv𝔣).1 (hα.cong v hv𝔣).2 (hα'.cong v hv𝔣).1
      (hα'.cong v hv𝔣).2
  · rw [hfac, archSign_mul K τ]
    exact iff_of_true (hα.sign τ) (hα'.sign τ)

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.mul"
private theorem isAdjuster_principal_self (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    IsAdjuster K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · have h1 : adjFinV K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α v = 1 := by
      unfold adjFinV; simp only [mul_inv_cancel, Units.val_one]
      exact fad_one_apply K v
    show Valued.v (adjFinV K _ α v) = 1 ∧ Valued.v (adjFinV K _ α v - 1) ≤ _
    rw [h1]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le'⟩
  · have h1 : (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α : (AdeleRing (𝓞 K) K)ˣ)
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ = 1 := mul_inv_cancel _
    rw [h1]; exact archSign_one K τ

private theorem adjFinV_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K)
      = adjFinV K u α' v * (adjFinV K u α v)⁻¹ := by
  have hkey := congrArg (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ =>
    ((x : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v)
    (congrArg (projFin K) (adj_adele_ratio K u α α'))
  rw [map_mul, map_inv, projFin_principal] at hkey
  simp only [Units.val_mul, fad_mul_apply, fad_units_inv_apply, projFin_val] at hkey
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 K) K (α * α'⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) from by
    rw [FiniteAdeleRing.unitEmbedding_apply]; exact FiniteAdeleRing.algebraMap_apply ..] at hkey
  rw [← hkey, mul_comm]; rfl

private theorem valuation_ratio_sub_one_le {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α')
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K (((α * α'⁻¹ : Kˣ) : K) - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  rw [← v.valuedAdicCompletion_eq_valuation']
  have hcoe : ((((α * α'⁻¹ : Kˣ) : K) - 1 : K) : v.adicCompletion K)
      = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) - 1 := by
    have h := map_sub (algebraMap K (v.adicCompletion K)) (((α * α'⁻¹ : Kˣ) : K)) 1
    rw [map_one] at h
    exact h
  rw [hcoe, adjFinV_ratio K u α α']
  exact unit_cong_div K (hα'.cong v hv).2 (hα.cong v hv).1 (hα.cong v hv).2

private theorem ratio_totally_positive {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') (τ : K →+* ℝ) :
    0 < τ ((α * α'⁻¹ : Kˣ) : K) := by
  rw [← archSign_principal K τ, show Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'⁻¹)
    = pK K (α * α'⁻¹) from rfl, map_mul, map_inv, archSign_mul K τ, archSign_inv K τ]
  have h1 : archSign K τ u ↔ archSign K τ (pK K α) := by
    have := hα.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  have h2 : archSign K τ u ↔ archSign K τ (pK K α') := by
    have := hα'.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  exact h1.symm.trans h2

private theorem valuation_eq_one_of_cong {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : K}
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (β - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K β = 1 := by
  have hm1 : 1 ≤ idealMultiplicity K v 𝔣 := by
    unfold idealMultiplicity
    rwa [Nat.one_le_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible]
  have hlt : v.valuation K (β - 1) < 1 :=
    lt_of_le_of_lt (hcong v hv) (by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_lt_exp]
      omega)
  have hβ : β = (β - 1) + 1 := (sub_add_cancel β 1).symm
  rw [hβ, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

private theorem count_spanSingleton_eq_zero_of_valuation_eq_one {β : Kˣ}
    (v : HeightOneSpectrum (𝓞 K)) (h : v.valuation K (β : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 := by
  rw [← placeOrd_unitEmbedding]
  unfold placeOrd
  rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
    FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (β : K), h,
    WithZero.log_one, neg_zero]

private theorem mem_modulus_of_forall_valuation_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {x : 𝓞 K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (algebraMap (𝓞 K) K x) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    x ∈ 𝔣 := by
  have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [← Ideal.iInf_maxPowDividing_eq h𝔣0, Submodule.mem_iInf]
  intro v
  show x ∈ v.asIdeal ^ (idealMultiplicity K v 𝔣)
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := K)]
    exact hx v hv
  · have hm0 : idealMultiplicity K v 𝔣 = 0 := by
      unfold idealMultiplicity
      by_contra hne
      exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hne)
    simp [hm0]

private theorem toPrincipalIdeal_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : Kˣ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (hsign : ∀ τ : K →+* ℝ, 0 < τ (β : K)) :
    toPrincipalIdeal (𝓞 K) K β ∈ narrowRaySubgroup K 𝔣 := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_valuation_eq_one K v
      (valuation_eq_one_of_cong K h𝔣 hcong v hv)

  obtain ⟨d, hd0, hd1, n, hn⟩ := movingLemma K h𝔣 (β : K) β.ne_zero hloc

  have hd0' : (algebraMap (𝓞 K) K) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at hn
    exact β.ne_zero ((mul_eq_zero.mp hn.symm).resolve_left hd0')

  have hnd1 : n - d ∈ 𝔣 := by
    refine mem_modulus_of_forall_valuation_le K h𝔣 fun v hv => ?_
    have hval_d : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [v.valuation_of_algebraMap (K := K)]
      refine le_antisymm (v.intValuation_le_one d) ?_
      rw [← not_lt, v.intValuation_lt_one_iff_mem]
      intro hmem
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (show (1 : 𝓞 K) ∈ v.asIdeal from by
          have : (d : 𝓞 K) - (d - 1) ∈ v.asIdeal := sub_mem hmem
            ((Ideal.dvd_iff_le.mp hv) hd1)
          simpa using this))
    have hsplit : (algebraMap (𝓞 K) K) (n - d)
        = algebraMap (𝓞 K) K d * ((β : K) - 1) := by
      rw [map_sub, hn]; ring
    rw [hsplit, map_mul, hval_d, one_mul]
    exact hcong v hv
  have hn1 : n - 1 ∈ 𝔣 := by
    have : n - 1 = (n - d) + (d - 1) := by ring
    rw [this]; exact add_mem hnd1 hd1

  have hn0' : (algebraMap (𝓞 K) K) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0
  have hsgn : ∀ τ : K →+* ℝ, (0 < τ (algebraMap (𝓞 K) K n))
      ↔ (0 < τ (algebraMap (𝓞 K) K d)) := by
    intro τ
    have hτβ : 0 < τ (β : K) := hsign τ
    rw [show (algebraMap (𝓞 K) K) n = (algebraMap (𝓞 K) K) d * (β : K) from hn,
      map_mul]
    refine ⟨fun h => ?_, fun h => mul_pos h hτβ⟩
    exact ((mul_pos_iff.mp h).resolve_right fun ⟨_, hb⟩ => hb.not_gt hτβ).1

  set yn : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K n hn0, principalUnit_mem_coprimeToModulus K hn0 hn1⟩ with hyn_def
  set yd : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K d hd0, principalUnit_mem_coprimeToModulus K hd0 hd1⟩ with hyd_def
  have hyn_val : ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K n hn0
  have hyd_val : ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K d hd0

  have hyd2 : ((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hd0 hd1 hyd_val hd0 hd1 hyd_val
      fun _ => Iff.rfl)
  have hynyd : ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hn0 hn1 hyn_val hd0 hd1 hyd_val
      hsgn)

  have hβnd' : toPrincipalIdeal (𝓞 K) K β * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_mul, hyn_val, hyd_val, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm, hn]
  have hβnd : toPrincipalIdeal (𝓞 K) K β
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹ :=
    eq_mul_inv_of_mul_eq hβnd'

  rw [hβnd]
  have hrw : (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹
      = (((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
        * ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      show ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
          * ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))
        = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) from by
          rw [mul_comm (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) _, ← mul_assoc, inv_mul_cancel,
            one_mul],
      mul_comm]
  rw [hrw]
  exact mul_mem (inv_mem hyd2) hynyd

private theorem mk_eq_mk_of_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') :
    NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩
      = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα'.coprime⟩ := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  show (fadContentHom K (projFin K _))⁻¹ * fadContentHom K (projFin K _) ∈ _
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, adj_adele_ratio K u α α',
    projFin_principal, fadContentHom_unitEmbedding]
  exact toPrincipalIdeal_mem_narrowRaySubgroup K h𝔣 (α * α'⁻¹)
    (fun v hv => valuation_ratio_sub_one_le K hα hα' v hv)
    (fun τ => ratio_totally_positive K hα hα' τ)

end StageC

end HeckeCharacter

end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain AbsoluteValue"

open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace ComplexEmbedding.isReal_iff FinitePlace.norm_lt_one_iff_mem FinitePlace.mk InfinitePlace.embedding_of_isReal_apply RingOfIntegers.mapRingHom InfinitePlace.map_natCast mk InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal InfinitePlace.mk AdeleRing.algebraMap_fst_apply InfinitePlace.Completion FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal InfinitePlace.eq_iff_isEquiv RingOfIntegers of_intermediateField RingOfIntegers.coe_injective HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace AdeleRing FinitePlace.embedding_apply InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply RingOfIntegers.ext FinitePlace.embedding ComplexEmbedding.conjugate_coe_eq PrimeNormIndex.secondInequalityCTM_of_finrank_eq_three"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem pos_iff norm_embedding embedding_apply embedding" end FinitePlace
namespace FinitePlace
p2m_open_scoped "NumberField.FinitePlace" in
private theorem _root_.NumberField.FinitePlace.isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk v).1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr v.ne_bot)
    exact ⟨x, hx, fun h => hx0 (h ▸ Ideal.zero_mem _)⟩
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx0
  · show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x) ≠ 1
    rw [show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x)
        = ‖FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ from rfl]
    exact ((FinitePlace.norm_lt_one_iff_mem K v x).mpr hx).ne

end FinitePlace
p2m_export "NumberField" "FinitePlace.isNontrivial"
p2m_open_scoped "NumberField.FinitePlace" in
private theorem FinitePlace.not_isEquiv_of_ne {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬ (FinitePlace.mk v₁).1.IsEquiv (FinitePlace.mk v₂).1 := by
  rw [isEquiv_iff_lt_one_iff]
  push Not
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h (HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le (HeightOneSpectrum.isMaximal v₁) Ideal.IsPrime.ne_top' H))
  refine ⟨algebraMap (𝓞 K) K x, ?_⟩
  rw [show ((FinitePlace.mk v₁).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₁ y‖ from rfl,
    show ((FinitePlace.mk v₂).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₂ y‖ from rfl]
  simp only
  exact Or.inl ⟨(FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1,
    ((FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2).ge⟩

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "embedding_of_isReal_apply IsReal Completion.extensionEmbeddingOfIsReal_coe embedding_mk_eq_of_isReal mk Completion embedding_of_isReal eq_iff_isEquiv ext comap pos_iff isReal_iff apply embedding Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply" end InfinitePlace
p2m_open_scoped "NumberField.InfinitePlace" in
private theorem InfinitePlace.not_isEquiv_finitePlace (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (FinitePlace.mk v).1 := by
  intro hequiv
  have hw2 : ¬ w.1 (2 : K) ≤ 1 := by
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [← InfinitePlace.coe_apply, this, InfinitePlace.map_natCast w 2]
    norm_num
  have hv2 : (FinitePlace.mk v).1 (2 : K) ≤ 1 := by
    show ‖FinitePlace.embedding v (2 : K)‖ ≤ 1
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [FinitePlace.norm_embedding, this]
    exact HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  exact hw2 (hequiv.le_one_iff.mpr hv2)

private noncomputable def mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (·.1) (fun v => (FinitePlace.mk v.1).1)

private theorem mixedAbs_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : InfinitePlace K ⊕ ↥S) : (mixedAbs K S i).IsNontrivial := by
  rcases i with w | v
  · exact InfinitePlace.isNontrivial w
  · exact FinitePlace.isNontrivial K v.1

private theorem mixedAbs_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (mixedAbs K S i).IsEquiv (mixedAbs K S j) := by
  intro i j hij
  match i, j with
  | Sum.inl w, Sum.inl w' =>
    exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp (by simpa using hij)
  | Sum.inl w, Sum.inr v => exact InfinitePlace.not_isEquiv_finitePlace K w v.1
  | Sum.inr v, Sum.inl w =>
    exact fun h => InfinitePlace.not_isEquiv_finitePlace K w v.1 h.symm
  | Sum.inr v, Sum.inr v' =>
    exact FinitePlace.not_isEquiv_of_ne K (by simpa using hij)

private theorem denseRange_algebraMap_pi_mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (mixedAbs K S i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (mixedAbs_isNontrivial K S) (mixedAbs_pairwise_not_isEquiv K S)
  let y := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (mixedAbs K S i) (z i)
  have htend : Filter.atTop.Tendsto
      (fun n i ↦ (WithAbs.equiv (mixedAbs K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : mixedAbs K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (mixedAbs K S i)) hw (z w)]
      have haw0 : a w ≠ 0 := fun ha => by
        have := (hx w).1; rw [ha, map_zero] at this; linarith
      have hu : 1 < mixedAbs K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(mixedAbs K S u).pos_iff.2 haw0, (hx w).2 u hw⟩
      have := (mixedAbs K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (mixedAbs K S u)).symm (WithAbs.equiv (mixedAbs K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

end NumberField

end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem sign_eq_of_withAbs_dist_lt (τ : K →+* ℝ) (α t : K) (ht : t ≠ 0)
    (h : (placeOf K τ).1 (α - t) < (placeOf K τ).1 t) :
    (0 < τ α ↔ 0 < τ t) := by

  have hval : ∀ x : K, (placeOf K τ).1 x = |τ x| := by
    intro x
    rw [← InfinitePlace.coe_apply]
    show (InfinitePlace.mk (Complex.ofRealHom.comp τ)) x = |τ x|
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hval, map_sub] at h

  have ht0 : τ t ≠ 0 := fun h0 => ht ((map_eq_zero τ).mp h0)
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · refine ⟨fun hα => absurd ?_ (not_lt.mpr hα.le), fun hα => absurd hα hneg.not_gt⟩
    calc τ α = τ t + (τ α - τ t) := by ring
      _ < 0 := by
        have := abs_lt.mp h
        linarith [abs_of_neg hneg ▸ this.2]
  · refine ⟨fun _ => hpos, fun _ => ?_⟩
    calc (0 : ℝ) < τ t - |τ α - τ t| := by linarith [abs_of_pos hpos ▸ h]
      _ ≤ τ t - (τ t - τ α) := by linarith [neg_abs_le (τ α - τ t)]
      _ = τ α := by ring

private noncomputable def primesOf (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])).toFinset

private theorem mem_primesOf {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ primesOf K 𝔣 h𝔣 ↔ v.asIdeal ∣ 𝔣 :=
  Set.Finite.mem_toFinset _

private noncomputable def fadComp (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem fadComp_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    fadComp K u v ≠ 0 := by
  intro h
  exact valued_ne_zero_of_unit K (projFin K u) v (by rw [projFin_val, ← fadComp, h, map_zero])

private theorem archRealProjTau_principal (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = τ (α : K) := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_placeOf]
  rfl

private theorem exists_embedding_near_fadComp (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < ε := by
  obtain ⟨t, ht⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap K) (fadComp K u v) ε hε
  exact ⟨t, by rw [FinitePlace.embedding_apply]; rwa [dist_comm, dist_eq_norm] at ht⟩

private theorem cong_of_completion_close {v : HeightOneSpectrum (𝓞 K)} {α : K} {U : v.adicCompletion K}
    (hU : U ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ‖FinitePlace.embedding v α - U‖ < ‖U‖ * δ) :
    ‖U * (FinitePlace.embedding v α)⁻¹‖ = 1 ∧
    ‖U * (FinitePlace.embedding v α)⁻¹ - 1‖ ≤ δ := by
  set αv := FinitePlace.embedding v α with hαv
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hlt : ‖αv - U‖ < ‖U‖ :=
    h.trans_le (by nlinarith)
  have hαeq : ‖αv‖ = ‖U‖ := by
    have hne : ‖U‖ ≠ ‖αv - U‖ := (hlt.trans_le (le_refl _)).ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := U) (y := αv - U) hne
    rw [add_sub_cancel, max_eq_left hlt.le] at this
    exact this
  have hα0 : αv ≠ 0 := fun h0 => by simp [h0] at hαeq; exact hU (norm_eq_zero.mp hαeq.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_inv, hαeq, mul_inv_cancel₀ hUpos.ne']
  · have hfac : U * αv⁻¹ - 1 = (U - αv) * αv⁻¹ := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hαeq, norm_sub_rev]
    calc ‖αv - U‖ * ‖U‖⁻¹ ≤ (‖U‖ * δ) * ‖U‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right h.le (inv_nonneg.mpr hUpos.le)
      _ = δ := by field_simp

private theorem adjCompEq (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
      = fadComp K u v * (FinitePlace.embedding v (α : K))⁻¹ := by
  have hmul : ((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = (u : AdeleRing (𝓞 K) K).2
        * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul]; rfl
  rw [hmul, fad_mul_apply K, ← fadComp]
  congr 1
  rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
    FinitePlace.embedding_apply]
  show ((algebraMap K (AdeleRing (𝓞 K) K)) ((α : K)⁻¹)).2 v = _
  rw [show ∀ x : K, ((algebraMap K (AdeleRing (𝓞 K) K)) x).2 v
      = algebraMap K (v.adicCompletion K) x from fun x => rfl,
    map_inv₀]
  rfl

private theorem valued_cong_of_norm_cong {v : HeightOneSpectrum (𝓞 K)} {X Y : v.adicCompletion K}
    (h1 : ‖X‖ = 1) (h2 : ‖X - 1‖ ≤ ‖Y‖) :
    Valued.v X = 1 ∧ Valued.v (X - 1) ≤ Valued.v Y := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (Valued.toNormedField.norm_le_one_iff).mp h1.le
  · exact (Valued.toNormedField.one_le_norm_iff).mp h1.ge
  · exact (Valued.toNormedField.norm_le_iff).mp h2

private theorem exists_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  set S := primesOf K 𝔣 h𝔣 with hS

  obtain ⟨γ, hγ𝔣, hγ0⟩ : ∃ γ : 𝓞 K, γ ∈ 𝔣 ∧ γ ≠ 0 := by
    obtain ⟨γ, hγ𝔣, hγ0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h𝔣)
    exact ⟨γ, hγ𝔣, fun h => hγ0 (h ▸ Ideal.zero_mem ⊥)⟩
  have hγK0 : (γ : K) ≠ 0 := by exact_mod_cast hγ0

  have hγemb_ne : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.embedding v (γ : K) ≠ 0 :=
    fun v => (map_ne_zero _).mpr hγK0
  have hγnorm_pos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖FinitePlace.embedding v (γ : K)‖ :=
    fun v => norm_pos_iff.mpr (hγemb_ne v)
  have hγnorm_le_one : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v (γ : K)‖ ≤ 1 := by
    intro v
    rw [Valued.toNormedField.norm_le_one_iff,
      show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one γ
  have hγval_le : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (FinitePlace.embedding v (γ : K))
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
    intro v _
    rw [show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    refine (v.intValuation_le_pow_iff_dvd γ _).mpr
      (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hγ𝔣))))
    have h𝔣0 : (Associates.mk 𝔣) ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
    have hirr := Associates.irreducible_mk.mpr v.irreducible
    have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr
        (k := idealMultiplicity K v 𝔣)).mpr le_rfl
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this

  have hUpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖fadComp K u v‖ :=
    fun v => norm_pos_iff.mpr (fadComp_ne_zero K u v)

  set bnd : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ with hbnd
  have hbnd_pos : ∀ v, 0 < bnd v := fun v => mul_pos (hUpos v) (hγnorm_pos v)
  obtain ⟨r, hr0, hr1, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ v ∈ S, r < bnd v := by
    by_cases hne : S.Nonempty
    · have hm_pos : 0 < S.inf' hne bnd :=
        (Finset.lt_inf'_iff hne).mpr (fun v _ => hbnd_pos v)
      refine ⟨min (1/2) (S.inf' hne bnd / 2), ?_, ?_, ?_⟩
      · exact lt_min (by norm_num) (by linarith)
      · exact (min_le_left _ _).trans_lt (by norm_num)
      · intro v hv
        refine (min_le_right _ _).trans_lt ?_
        have hle := Finset.inf'_le bnd hv
        linarith [hbnd_pos v]
    · exact ⟨1/2, by norm_num, by norm_num, fun v hv => absurd ⟨v, hv⟩ hne⟩

  have htv : ∀ v ∈ S, ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < r :=
    fun v _ => exists_embedding_near_fadComp K u v hr0
  choose tv htv using htv

  set archTgt : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if archSign K (InfinitePlace.embedding_of_isReal hw) u then (1:K) else (-1:K))
    else (1:K) with harchTgt
  have harchTgt_ne : ∀ w, archTgt w ≠ 0 := by
    intro w; unfold archTgt; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have harchTgt_abs : ∀ w : InfinitePlace K, w (archTgt w) = 1 := by
    intro w; unfold archTgt; split_ifs
    · exact map_one _
    · exact (w.1.map_neg 1).trans (map_one _)
    · exact map_one _

  set z : InfinitePlace K ⊕ ↥S → K := Sum.elim archTgt (fun v => tv v.1 v.2) with hz

  obtain ⟨α, hα⟩ := Metric.denseRange_iff.mp
    (NumberField.denseRange_algebraMap_pi_mixedAbs K S)
    (fun i => (WithAbs.equiv (NumberField.mixedAbs K S i)).symm (z i)) r hr0
  have hα_at : ∀ i, (NumberField.mixedAbs K S i) (α - z i) < r := by
    intro i
    have hi := (dist_pi_lt_iff hr0).mp hα i
    rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hi
    convert hi using 2 <;> first | rfl | simp [Pi.algebraMap_apply, WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs]

  have hα0 : α ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    intro h
    have := hα_at (Sum.inl w)
    simp only [hz, Sum.elim_inl, h, zero_sub] at this
    have heq : (NumberField.mixedAbs K S (Sum.inl w)) (-archTgt w) = 1 := by
      change (w.1 : AbsoluteValue K ℝ) (-archTgt w) = 1
      rw [(w.1).map_neg, ← InfinitePlace.coe_apply, harchTgt_abs w]
    rw [heq] at this; linarith
  refine ⟨Units.mk0 α hα0, ?_, ?_⟩
  ·
    intro v hv
    have hvS : v ∈ S := (mem_primesOf K h𝔣 v).mpr hv
    rw [adjCompEq K u (Units.mk0 α hα0) v, Units.val_mk0]

    have hstep : ‖FinitePlace.embedding v α - fadComp K u v‖
        < ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ := by
      have hα_fin := hα_at (Sum.inr ⟨v, hvS⟩)
      simp only [hz, Sum.elim_inr, NumberField.mixedAbs] at hα_fin

      have h1 : ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖ < r := by
        rw [← map_sub]; exact hα_fin
      have h2 := htv v hvS
      calc ‖FinitePlace.embedding v α - fadComp K u v‖
          ≤ max ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖
              ‖FinitePlace.embedding v (tv v hvS) - fadComp K u v‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact IsUltrametricDist.dist_triangle_max _ _ _
        _ < r := max_lt h1 h2
        _ < bnd v := hrS v hvS
    have hcong := cong_of_completion_close K (fadComp_ne_zero K u v)
      (hγnorm_pos v) (hγnorm_le_one v) hstep
    have hbr := valued_cong_of_norm_cong K hcong.1 hcong.2
    exact ⟨hbr.1, hbr.2.trans (hγval_le v hv)⟩
  ·
    intro τ
    rw [archSign_mul K τ, archSign_inv K τ]
    show archSign K τ u ↔ archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.mk0 α hα0))
    unfold archSign
    rw [archRealProjTau_principal K τ (Units.mk0 α hα0), Units.val_mk0]

    have hwτ := isReal_placeOf K τ
    have htgt_τ : archTgt (placeOf K τ)
        = if (0:ℝ) < archRealProjTau K τ u then (1:K) else (-1:K) := by
      unfold archTgt; rw [dif_pos hwτ]
      congr 1
      · unfold archSign
        rw [show InfinitePlace.embedding_of_isReal hwτ = τ from embedding_of_isReal_placeOf K τ]
    have habs_tgt : (placeOf K τ) (archTgt (placeOf K τ)) = 1 := harchTgt_abs _
    have hclose : (placeOf K τ) (α - archTgt (placeOf K τ)) < (placeOf K τ) (archTgt (placeOf K τ)) := by
      rw [habs_tgt]
      have := hα_at (Sum.inl (placeOf K τ))
      simp only [hz, Sum.elim_inl, NumberField.mixedAbs] at this
      exact this.trans hr1
    have hsign_iff := sign_eq_of_withAbs_dist_lt K τ α (archTgt (placeOf K τ))
      (harchTgt_ne _) hclose
    constructor
    · intro hpos
      refine hsign_iff.mpr ?_
      rw [htgt_τ, if_pos hpos, map_one]; exact one_pos
    · intro hτα
      by_contra hneg
      have hlt : (0:ℝ) < -1 := by
        have := hsign_iff.mp hτα
        rwa [htgt_τ, if_neg hneg, map_neg, map_one] at this
      linarith

end HeckeCharacter

end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply WithZero"

open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private abbrev adjFinV_ic (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm_ic {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK_ic : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_mul_ic (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK_ic K (α * α'))⁻¹ = (u * (pK_ic K α)⁻¹) * (u' * (pK_ic K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm_ic _ _ _ _

private def ideleContentHom (𝔣 : Ideal (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* NarrowRayClassGroup K 𝔣 := by
  classical
  by_cases h𝔣 : 𝔣 = ⊥
  · exact 1
  · exact
      { toFun := fun u => NarrowRayClassGroup.mk K 𝔣
          ⟨_, (Classical.choose_spec (exists_isAdjuster K h𝔣 u)).coprime⟩
        map_one' := by
          rw [mk_eq_mk_of_isAdjuster K h𝔣
            (Classical.choose_spec (exists_isAdjuster K h𝔣 1)) (isAdjuster_one_one K 𝔣)]
          simp only [map_one, inv_one, mul_one]; rfl
        map_mul' := fun u u' => by
          have hαu := Classical.choose_spec (exists_isAdjuster K h𝔣 u)
          have hαu' := Classical.choose_spec (exists_isAdjuster K h𝔣 u')
          have hαuu' : IsAdjuster K 𝔣 (u * u') (_ * _) := IsAdjuster.mul K hαu hαu'
          rw [mk_eq_mk_of_isAdjuster K h𝔣
              (Classical.choose_spec (exists_isAdjuster K h𝔣 (u * u'))) hαuu',
            ← (NarrowRayClassGroup.mk K 𝔣).map_mul ⟨_, hαu.coprime⟩ ⟨_, hαu'.coprime⟩]
          refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
          show fadContentHom K (projFin K _) = fadContentHom K (projFin K _)
            * fadContentHom K (projFin K _)
          rw [← map_mul, ← map_mul, adj_adele_mul_ic K u u'] }

private theorem ideleContentHom_apply {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (hα : IsAdjuster K 𝔣 u α) :
    ideleContentHom K 𝔣 u = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩ := by
  unfold ideleContentHom
  rw [dif_neg h𝔣]
  exact mk_eq_mk_of_isAdjuster K h𝔣 (Classical.choose_spec (exists_isAdjuster K h𝔣 u)) hα

private theorem ideleContentHom_principal (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    ideleContentHom K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · unfold ideleContentHom; rw [dif_pos h𝔣]; rfl
  · rw [ideleContentHom_apply K h𝔣 (isAdjuster_principal_self K 𝔣 α)]
    have h1 : fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)) = 1 := by
      rw [mul_inv_cancel, map_one, map_one]
    rw [show (⟨_, (isAdjuster_principal_self K 𝔣 α).coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1
      from Subtype.ext h1, map_one]

private theorem ideleContentHom_uniformizerIdele_v2 (𝔣 : Ideal (𝓞 K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1)
    (huv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = WithZero.exp (-1 : ℤ))
    (hu𝔣 : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w - 1)
        ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = primeClass K 𝔣 v hv := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣; simp only [show v.asIdeal ∣ (⊥ : Ideal (𝓞 K)) from ⟨0, (mul_zero _).symm⟩,
      not_true] at hv
  ·
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun w hw𝔣 => ?_, fun τ => ?_⟩
      · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
        show Valued.v (adjFinV_ic K u 1 w) = 1 ∧ Valued.v (adjFinV_ic K u 1 w - 1) ≤ _
        have hu1 : adjFinV_ic K u 1 w = (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
            w) := by unfold adjFinV_ic; simp only [map_one, inv_one, mul_one]
        rw [hu1]
        exact ⟨huw w hwv, hu𝔣 w hw𝔣⟩
      · simp only [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ huarch
    rw [ideleContentHom_apply K h𝔣 hadj]

    refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
    show fadContentHom K (projFin K (u * (pK_ic K 1)⁻¹)) = primeUnit K v
    rw [map_one, inv_one, mul_one, fadContentHom_apply]
    refine finprod_eq_single (fun w => primeUnit K w ^ placeOrd K (projFin K u) w) v
      ?_ |>.trans ?_
    · intro w hwv
      show primeUnit K w ^ placeOrd K (projFin K u) w = 1
      rw [show placeOrd K (projFin K u) w = 0 from
        (placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ huw w hwv), zpow_zero]
    · show primeUnit K v ^ placeOrd K (projFin K u) v = primeUnit K v
      rw [show placeOrd K (projFin K u) v = 1 from by
        unfold placeOrd; rw [projFin_val, huv, WithZero.log_exp, neg_neg], zpow_one]

end HeckeCharacter

end

end

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

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

end Artin

end LanglandsTunnell.P2.Artin

end

end

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

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

end LanglandsTunnell.P2.Artin

end

end

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply"

open scoped IsMulCommutative nonZeroDivisors

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

end LanglandsTunnell.P2.Artin

end

end

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
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

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (placeUnder' k E w).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (placeUnder' k E w).isPrime (placeUnder' k E w).ne_bot
  haveI : w.asIdeal.LiesOver (placeUnder' k E w).asIdeal :=
    ⟨(placeUnder'_asIdeal k E w).symm⟩
  rw [fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0,
    ← FractionalIdeal.coeIdeal_pow]
  exact congrArg _ (by
    haveI := w.isMaximal; haveI := (placeUnder' k E w).isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' k E w).asIdeal).symm)

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top,
      FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero
        (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ)
        = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    ((fracRelNormUnit k E (principalUnit E α hα) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.span {Algebra.intNorm (𝓞 k) (𝓞 E) α} : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    fracRelNormUnit_mk0 k E, Ideal.relNorm_singleton]

end HeckeCharacter

end

end

section

set_option autoImplicit false

set_option maxHeartbeats 3200000

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField"

namespace M4aP2

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem prod_sub_one_mem {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i - 1 ∈ J) :
    (∏ i ∈ s, f i) - 1 ∈ J := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hsplit : f a * ∏ i ∈ s, f i - 1 = f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    exact J.add_mem (Ideal.mul_mem_left _ _ h2) h1

private abbrev NCl := ↥(IntermediateField.normalClosure k E (AlgebraicClosure k))

@[reducible] private noncomputable def algONcl : Algebra (𝓞 k) (𝓞 (NCl k E)) :=
  (RingOfIntegers.mapRingHom (algebraMap k (NCl k E))).toAlgebra

attribute [local instance] algONcl

omit [NumberField k] [NumberField E] in
private theorem algONcl_coe (x : 𝓞 k) :
    (algebraMap (𝓞 k) (𝓞 (NCl k E)) x : NCl k E) = algebraMap k (NCl k E) (x : k) := rfl

omit [NumberField k] [NumberField E] in
private theorem algONcl_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
  intro a b h
  have h1 : algebraMap k (NCl k E) (a : k) = algebraMap k (NCl k E) (b : k) := by
    rw [← algONcl_coe, ← algONcl_coe, h]
  exact FaithfulSMul.algebraMap_injective (𝓞 k) k ((algebraMap k (NCl k E)).injective h1)

private scoped instance : IsScalarTower ℤ (𝓞 k) (𝓞 (NCl k E)) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private scoped instance : FaithfulSMul (𝓞 k) (𝓞 (NCl k E)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algONcl_injective k E)

variable {k E}

private noncomputable def embO (σ : E →ₐ[k] AlgebraicClosure k) :
    𝓞 E →+* 𝓞 (NCl k E) :=
  RingOfIntegers.mapRingHom
    ((σ.codRestrict _ fun x => σ.fieldRange_le_normalClosure ⟨x, rfl⟩ :
      E →ₐ[k] NCl k E) : E →+* NCl k E)

omit [NumberField k] [NumberField E] in
private theorem embO_coe (σ : E →ₐ[k] AlgebraicClosure k) (x : 𝓞 E) :
    algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ x : 𝓞 (NCl k E)) : NCl k E)
    = σ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField k] [NumberField E] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem embO_comp (σ : E →ₐ[k] AlgebraicClosure k) :
    (embO σ).comp (algebraMap (𝓞 k) (𝓞 E)) = algebraMap (𝓞 k) (𝓞 (NCl k E)) := by
  apply RingHom.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
  show (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
      E →ₐ[k] NCl k E) (algebraMap k E (x : k))
    = algebraMap k (NCl k E) (x : k)
  exact (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
    E →ₐ[k] NCl k E).commutes (x : k)

variable (k E)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
    (hy : y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 E))) :
    Algebra.intNorm (𝓞 k) (𝓞 E) y - 1 ∈ 𝔠 := by
  classical
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E

  have hmem : ∀ σ : E →ₐ[k] AlgebraicClosure k,
      embO σ y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    intro σ
    have h1 : embO σ (y - 1) ∈ (𝔠.map (algebraMap (𝓞 k) (𝓞 E))).map (embO σ) :=
      Ideal.mem_map_of_mem (embO σ) hy
    rw [Ideal.map_map, embO_comp σ] at h1
    simpa [map_sub] using h1
  have hPsub : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y) - 1
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) :=
    prod_sub_one_mem _ _ _ fun σ _ => hmem σ

  have hPeq : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y)
      = algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
    apply RingHom.injective (algebraMap (NCl k E) (AlgebraicClosure k))
    rw [show ((algebraMap (𝓞 (NCl k E)) (NCl k E))
        (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y))
        = ∏ σ : E →ₐ[k] AlgebraicClosure k,
          ((embO σ y : 𝓞 (NCl k E)) : NCl k E) from map_prod _ _ _,
      map_prod]
    have hL : ∀ σ : E →ₐ[k] AlgebraicClosure k,
        algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ y : 𝓞 (NCl k E)) : NCl k E)
        = σ (algebraMap (𝓞 E) E y) := fun σ => embO_coe σ y
    rw [Finset.prod_congr rfl fun σ _ => hL σ]
    have hR : algebraMap (NCl k E) (AlgebraicClosure k)
        ((algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) : NCl k E))
        = algebraMap k (AlgebraicClosure k)
          (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
      rw [algONcl_coe]
      exact (IsScalarTower.algebraMap_apply k (NCl k E) (AlgebraicClosure k) _).symm
    rw [hR, Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact (Algebra.norm_eq_prod_embeddings (K := k) (L := E)
      (E := AlgebraicClosure k) _).symm

  have hfin : algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y - 1)
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    rw [map_sub, map_one, ← hPeq]
    exact hPsub
  haveI hTF : Module.IsTorsionFree (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFlat : Module.Flat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFF : Module.FaithfullyFlat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := 𝓞 k) (B := 𝓞 (NCl k E)) 𝔠]
  exact Ideal.mem_comap.mpr hfin

private theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
    (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E y)) :
    ∀ τ' : k →+* ℝ, 0 < τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
  intro τ'
  classical
  letI : Algebra k ℂ := (Complex.ofRealHom.comp τ').toAlgebra
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  set yE : E := algebraMap (𝓞 E) E y with hyEdef
  have hyE0 : yE ≠ 0 := fun h =>
    hy0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h)
  have hσ0 : ∀ σ : E →ₐ[k] ℂ, σ yE ≠ 0 := fun σ h =>
    hyE0 ((map_eq_zero_iff _ (RingHom.injective (σ : E →+* ℂ))).mp h)
  have hstar_alg : ∀ c : k, (starRingEnd ℂ) (algebraMap k ℂ c) = algebraMap k ℂ c := fun c =>
    Complex.conj_ofReal _
  let conjA : (E →ₐ[k] ℂ) → (E →ₐ[k] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp (σ : E →+* ℂ)
      commutes' := fun c => by
        show (starRingEnd ℂ) (σ (algebraMap k E c)) = algebraMap k ℂ c
        rw [σ.commutes]
        exact hstar_alg c }
  have hconjA_apply : ∀ (σ : E →ₐ[k] ℂ) (x : E), conjA σ x = (starRingEnd ℂ) (σ x) :=
    fun _ _ => rfl
  have hconjA_invol : ∀ σ, conjA (conjA σ) = σ := fun σ => AlgHom.ext fun x =>
    Complex.conj_conj (σ x)
  have hf_pair : ∀ σ : E →ₐ[k] ℂ,
      σ yE / (‖σ yE‖ : ℂ) * ((conjA σ) yE / (‖(conjA σ) yE‖ : ℂ)) = 1 := by
    intro σ
    have hz : σ yE ≠ 0 := hσ0 σ
    have hr0 : (‖σ yE‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : (conjA σ) yE = (starRingEnd ℂ) (σ yE) := rfl
    rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', ← sq]
    exact div_self (pow_ne_zero 2 hr0)
  have hf_fixed : ∀ σ : E →ₐ[k] ℂ, σ yE / (‖σ yE‖ : ℂ) ≠ 1 → conjA σ ≠ σ := by
    intro σ hf1 heq
    apply hf1
    have hreal : NumberField.ComplexEmbedding.IsReal (σ : E →+* ℂ) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have h1 := congrArg (fun ψ : E →ₐ[k] ℂ => ψ x) heq
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hconjA_apply] using h1
    have hτpos := hpos hreal.embedding
    have hval : σ yE = ((hreal.embedding yE : ℝ) : ℂ) := (hreal.coe_embedding_apply yE).symm
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
    exact div_self (Complex.ofReal_ne_zero.mpr hτpos.ne')
  have hprod1 : ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ)) = 1 :=
    Finset.prod_involution (fun σ _ => conjA σ) (fun σ _ => hf_pair σ)
      (fun σ _ h => hf_fixed σ h) (fun σ _ => Finset.mem_univ _) (fun σ _ => hconjA_invol σ)
  have hsplit : ∀ σ : E →ₐ[k] ℂ, σ yE = σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ) := fun σ =>
    (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hσ0 σ)))).symm
  have hprodR : ∏ σ : E →ₐ[k] ℂ, σ yE = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    calc ∏ σ : E →ₐ[k] ℂ, σ yE
        = ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ)) :=
          Finset.prod_congr rfl fun σ _ => hsplit σ
      _ = (∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ))) * ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) :=
          Finset.prod_mul_distrib
      _ = ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) := by rw [hprod1, one_mul]
  have hbridge : algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y))
      = ∏ σ : E →ₐ[k] ℂ, σ yE := by
    rw [Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact Algebra.norm_eq_prod_embeddings (K := k) (L := E) (E := ℂ) yE
  have hfinal : ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
      = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [show ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
        = algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) from rfl,
      hbridge, hprodR]
  have hval := Complex.ofReal_injective hfinal
  rw [hval]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hσ0 σ)

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

open scoped Classical in

private def fNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : NarrowRayClassGroup k 𝔠 :=
  if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
  then primeClass k 𝔠 (placeUnder' k E w) h ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)
  else 1

omit [NumberField E] in

private theorem fNC2_eq_mk_gcop (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    fNC2 k E 𝔠 w = NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 w) := by
  classical
  unfold fNC2 gcopNC2
  split
  · simp only [primeClass, ← map_pow]; rfl
  · rw [map_one]

private theorem coe_raySymbol_gcop_eq_fracRelNormUnit {𝔠 : Ideal (𝓞 k)} (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) :
    ((raySymbol E (gcopNC2 k E 𝔠)
        ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (principalUnit E α hα0) := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
  have hfRN : fracRelNormUnit k E (principalUnit E α hα0)
      = raySymbol E
          (fun w => primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)) J := by
    show raySymbol E _ ((principalUnit E α hα0 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
        FractionalIdeal ((𝓞 E)⁰) E) = _
    exact congrArg _ (principalUnit_val E α hα0)
  rw [hfRN]
  unfold raySymbol
  refine ((MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J))).trans ?_
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  ·
    have hct : FractionalIdeal.count E w J = 0 :=
      count_span_singleton_eq_zero_of_sub_one_mem E hα0 hα1
        ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  ·
    simp only [gcopNC2]
    rw [dif_pos hw]

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_hkill (𝔠 : Ideal (𝓞 k)) (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) :
    raySymbol E (fNC2 k E 𝔠)
      ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1 := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]

  apply NarrowRayClassGroup.mk_eq_one_of_mem

  rw [coe_raySymbol_gcop_eq_fracRelNormUnit k E α hα0 hα1]

  apply Subgroup.subset_closure
  rw [mem_narrowRaySet_iff]
  exact ⟨Algebra.intNorm (𝓞 k) (𝓞 E) α, intNorm_ne_zero k E hα0,
    M4aP2.intNorm_sub_one_mem_of_sub_one_mem k E 𝔠 α hα1,
    M4aP2.intNorm_totPos_of_totPos k E α hα0 hpos,
    fracRelNormUnit_principalUnit k E α hα0⟩

private def relNormRCG (𝔠 : Ideal (𝓞 k)) :
    NarrowRayClassGroup E (modulusExt k E 𝔠) →* NarrowRayClassGroup k 𝔠 :=
  raySymbolDescend E (fNC2 k E 𝔠)
    (fun α hα0 hα1 hpos => relNormRCG_hkill k E 𝔠 α hα0 hα1 hpos)

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

omit [NumberField k] [NumberField E] in

private theorem modulusExt_ne_bot {𝔠 : Ideal (𝓞 k)} (h𝔠 : 𝔠 ≠ ⊥) : modulusExt k E 𝔠 ≠ ⊥ := by
  intro h
  exact h𝔠 ((Ideal.map_eq_bot_iff_of_injective
    (f := algebraMap (𝓞 k) (𝓞 E)) (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))).mp h)

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_mk (𝔠 : Ideal (𝓞 k)) (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y)
      = NarrowRayClassGroup.mk k 𝔠
          ⟨fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ),
            fracRelNormUnit_mem_coprimeToModulus k E Y.2⟩ := by
  rw [relNormRCG, raySymbolDescend_mk]

  rw [raySymbolHom_apply]
  set J := ((Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]
  exact congrArg _ (Subtype.ext (coe_raySymbol_gcop_eq_fracRelNormUnit' k E _ Y.2))

private theorem fracRelNormUnit_principalUnit' (a : 𝓞 E) (ha : a ≠ 0) :
    fracRelNormUnit k E (principalUnit E a ha)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) a) (intNorm_ne_zero k E ha) :=
  Units.ext ((fracRelNormUnit_principalUnit k E a ha).trans
    (principalUnit_val k _ (intNorm_ne_zero k E ha)).symm)

private theorem toPrincipalIdeal_algebraMap (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          (fun h => ha (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) h)))
      = principalUnit K a ha :=
  Units.ext <| by
    rw [coe_toPrincipalIdeal, Units.val_mk0, principalUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]

private theorem fracRelNormUnit_toPrincipalIdeal (α : Eˣ) :
    fracRelNormUnit k E (toPrincipalIdeal (𝓞 E) E α)
      = toPrincipalIdeal (𝓞 k) k (Units.map (Algebra.norm k) α) := by

  obtain ⟨x, y, hy, hαxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (α : E)
  have hy0 : (y : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨y, hy⟩
  have hey : (algebraMap (𝓞 E) E) y ≠ 0 := fun h => hy0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)
  have hx0 : x ≠ 0 := by
    intro h; subst h
    exact α.ne_zero (hαxy.symm.trans (by simp))
  have hex : (algebraMap (𝓞 E) E) x ≠ 0 := fun h => hx0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)

  have hα_dec : α = Units.mk0 _ hex / Units.mk0 _ hey :=
    Units.ext (by rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hαxy])
  rw [hα_dec]
  simp only [map_div]

  rw [toPrincipalIdeal_algebraMap E x hx0, toPrincipalIdeal_algebraMap E y hy0,
    fracRelNormUnit_principalUnit' k E x hx0, fracRelNormUnit_principalUnit' k E y hy0]
  congr 1 <;>
    · rw [← toPrincipalIdeal_algebraMap k]
      exact congrArg _ (Units.ext (by
        simp only [Units.coe_map, Units.val_mk0]
        exact Algebra.algebraMap_intNorm (K := k) (L := E) _))

private theorem ideleContentHom_comp_ideleNorm (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 k) k)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 E) E)ˣ} {α : Eˣ},
      IsAdjuster E (modulusExt k E 𝔠) u α →
      IsAdjuster k 𝔠 (Nrm u) (Units.map (Algebra.norm k) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 E) E)ˣ,
      fadContentHom k (projFin k (Nrm u)) = fracRelNormUnit k E (fadContentHom E (projFin E u))) :
    (ideleContentHom k 𝔠).comp Nrm
      = (relNormRCG k E 𝔠).comp (ideleContentHom E (modulusExt k E 𝔠)) := by
  ext u
  have h𝔠E := modulusExt_ne_bot k E h𝔠
  obtain ⟨α, hα⟩ := exists_isAdjuster E h𝔠E u
  have hNα := hNrm_adjuster hα
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ideleContentHom_apply k h𝔠 hNα, ideleContentHom_apply E h𝔠E hα,
    relNormRCG_mk k E 𝔠]

  congr 1
  apply Subtype.ext
  show fadContentHom k (projFin k _) = fracRelNormUnit k E (fadContentHom E (projFin E _))
  simp only [map_mul, map_inv]
  rw [hNrm_fadContent u]
  congr 1
  rw [projFin_principal, projFin_principal, fadContentHom_unitEmbedding,
    fadContentHom_unitEmbedding, fracRelNormUnit_toPrincipalIdeal]

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (placeUnder' k E w)
          ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal) := by
  exact fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm

private theorem mk_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    NarrowRayClassGroup.mk k 𝔠 (relNormCTM k E 𝔠 Y)
      = relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y) :=
  (relNormRCG_mk k E 𝔠 Y).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section hcompat

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField Ideal NumberField.Ideal FrobeniusDensity Matrix FLT.ExplicitLift"

open LanglandsTunnell.P0

open scoped Pointwise

section FrobeniusGrain

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in

private theorem inertia_smul_eq_bot (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : 𝓞 L, g • x - x ∈ τ • Q := fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    [Finite (𝓞 L ⧸ (τ • Q))] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ := by
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)) (τ • Q) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹) (τ • Q) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end FrobeniusGrain
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Square

variable {I I' R R' : Type*} [Group I] [Group I'] [Group R] [Group R']

private theorem sup_range_eq_comap_range (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC' : Function.Surjective C') (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    P ⊔ Nrm.range = n.range.comap C := by
  apply le_antisymm
  · refine sup_le (fun p hp => ?_) ?_
    · rw [Subgroup.mem_comap, show C p = 1 from hP hp]
      exact one_mem _
    · rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_comap, ← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply]
      exact ⟨C' x, rfl⟩
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨r', hr'⟩ := hu
    obtain ⟨x, rfl⟩ := hC' r'
    have hx : C (Nrm x) = C u := by rw [← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply, hr']
    have hk : u * (Nrm x)⁻¹ ∈ C.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
    have hmem : u * (Nrm x)⁻¹ * Nrm x ∈ P ⊔ Nrm.range := mul_mem (hker hk) (Subgroup.mem_sup_right ⟨x, rfl⟩)
    rwa [inv_mul_cancel_right] at hmem

private theorem index_sup_range_eq (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC : Function.Surjective C) (hC' : Function.Surjective C')
    (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    (P ⊔ Nrm.range).index = n.range.index := by
  rw [sup_range_eq_comap_range C C' Nrm n P hsq hC' hker hP]
  exact (n.range).index_comap_of_surjective hC

end Square
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section IdealSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_eq_comap (𝔣 : Ideal (𝓞 K)) :
    normRaySubgroup K L 𝔣 = (relNormRCG K L 𝔣).range.comap (NarrowRayClassGroup.mk K 𝔣) := by
  refine sup_range_eq_comap_range (NarrowRayClassGroup.mk K 𝔣) (NarrowRayClassGroup.mk L (modulusExt K L 𝔣))
    (relNormCTM K L 𝔣) (relNormRCG K L 𝔣) _ (MonoidHom.ext fun Y => mk_relNormCTM K L Y) (QuotientGroup.mk'_surjective _)
    (fun x hx => Subgroup.mem_sup_left ?_) (fun x hx => ?_)
  · rwa [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  · rw [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx

private theorem normRaySubgroup_index_eq_index_range_relNormRCG (𝔣 : Ideal (𝓞 K)) :
    (normRaySubgroup K L 𝔣).index = (relNormRCG K L 𝔣).range.index := by
  rw [normRaySubgroup_eq_comap]
  exact ((relNormRCG K L 𝔣).range).index_comap_of_surjective (QuotientGroup.mk'_surjective _)

end IdealSide
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section IdeleSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev _root_.LanglandsTunnell.P2.Artin.principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range

p2m_export "LanglandsTunnell.P2.Artin" "principalIdeles"
private theorem normRaySubgroup_index_eq_idele_index (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hsurjK : Function.Surjective (ideleContentHom K 𝔣))
    (hsurjL : Function.Surjective (ideleContentHom L (modulusExt K L 𝔣)))
    (hkerK : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index := by
  rw [normRaySubgroup_index_eq_index_range_relNormRCG,
    index_sup_range_eq (ideleContentHom K 𝔣) (ideleContentHom L (modulusExt K L 𝔣)) Nrm (relNormRCG K L 𝔣) (principalIdeles K)
      (ideleContentHom_comp_ideleNorm K L 𝔣 h𝔣 Nrm hNrm_adjuster hNrm_fadContent) hsurjK hsurjL hkerK ?_]
  intro u hu
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hu
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end IdeleSide
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply IntermediateField"

open scoped nonZeroDivisors IsMulCommutative

section Field

variable (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem isGalois_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M) : IsGalois K F := by
  rw [← IsGalois.fixedField_fixingSubgroup F]
  infer_instance

end Field
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

set_option autoImplicit false

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hd

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section

set_option autoImplicit false

section

set_option autoImplicit false

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

open scoped nonZeroDivisors IsMulCommutative

section Carrier

variable (K : Type*) [Field K] [NumberField K]

@[scoped simp] private theorem coe_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    ((ctmInclusion K h x : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = (x : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := rfl

private theorem ctmInclusion_primeCarrier {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪) :
    ctmInclusion K h (primeCarrier K 𝔪 v hv) = primeCarrier K 𝔣 v (fun hv' => hv (dvd_trans hv' h)) := rfl

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

section Symbol

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem artinSymbol_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    artinSymbol K M 𝔣 (ctmInclusion K h x) = artinSymbol K M 𝔪 x := by
  show raySymbolHom K 𝔣 (artinFrob K M) _ = raySymbolHom K 𝔪 (artinFrob K M) _
  rw [raySymbolHom_apply, raySymbolHom_apply, coe_ctmInclusion]

end Symbol
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply IntermediateField"

open scoped IsMulCommutative Pointwise

section Mono

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M)

attribute [local instance] Ideal.Quotient.field

private theorem inertia_ne_bot_iff_ramificationIdxIn_ne_one (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ ↔ v.asIdeal.ramificationIdxIn (𝓞 L) ≠ 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v), ne_eq, ne_eq,
    Subgroup.card_eq_one]

private theorem ramificationIdxIn_ne_one_of_intermediateField (v : HeightOneSpectrum (𝓞 K))
    (h : v.asIdeal.ramificationIdxIn (𝓞 F) ≠ 1) : v.asIdeal.ramificationIdxIn (𝓞 M) ≠ 1 := by
  haveI := isGalois_intermediateField K M F
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have htower := Ideal.ramificationIdxIn_mul_ramificationIdxIn' (p := v.asIdeal) (primeAbove K F v) (F ≃ₐ[K] F) (𝓞 M)
    (M ≃ₐ[K] M) (M ≃ₐ[F] M)
  intro h1
  rw [h1] at htower
  exact h (Nat.eq_one_of_mul_eq_one_right htower)

namespace IsAdmissibleModulus
private theorem _root_.LanglandsTunnell.P2.Artin.IsAdmissibleModulus.of_intermediateField {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K M 𝔣) :
    IsAdmissibleModulus K F 𝔣 := by
  haveI := isGalois_intermediateField K M F
  refine ⟨h.1, fun v hv => h.2 v ?_⟩
  rw [inertia_ne_bot_iff_ramificationIdxIn_ne_one] at hv ⊢
  exact ramificationIdxIn_ne_one_of_intermediateField K M F v hv

end IsAdmissibleModulus
p2m_export "LanglandsTunnell.P2.Artin" "IsAdmissibleModulus.of_intermediateField"
end Mono
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

section

set_option autoImplicit false

section

set_option autoImplicit false

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter WithZero"

open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

local notation "pK" => Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)

section RayUnit

variable (𝔣 : Ideal (𝓞 K))

private def IsRayUnit (β : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ))) ∧
    ∀ τ : K →+* ℝ, 0 < τ (β : K)

variable {K 𝔣}

private theorem IsRayUnit.valuation_eq_one (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) : v.valuation K (β : K) = 1 :=
  valuation_eq_one_of_cong K h𝔣 h.1 v hv

private theorem isRayUnit_one : IsRayUnit K 𝔣 1 :=
  ⟨fun v _ => by rw [Units.val_one, sub_self, map_zero]; exact zero_le', fun τ => by rw [Units.val_one, map_one]; exact one_pos⟩

private theorem IsRayUnit.mul (h𝔣 : 𝔣 ≠ ⊥) {β β' : Kˣ} (h : IsRayUnit K 𝔣 β) (h' : IsRayUnit K 𝔣 β') : IsRayUnit K 𝔣 (β * β') := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_mul, map_mul]; exact mul_pos (h.2 τ) (h'.2 τ)⟩
  have heq : ((β * β' : Kˣ) : K) - 1 = (β : K) * ((β' : K) - 1) + ((β : K) - 1) := by push_cast; ring
  rw [heq]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (h.1 v hv))
  rw [map_mul, h.valuation_eq_one h𝔣 v hv, one_mul]
  exact h'.1 v hv

private theorem IsRayUnit.inv (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β) : IsRayUnit K 𝔣 β⁻¹ := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_inv_eq_inv_val, map_inv₀]; exact inv_pos.mpr (h.2 τ)⟩
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have heq : ((β⁻¹ : Kˣ) : K) - 1 = -(β : K)⁻¹ * ((β : K) - 1) := by
    rw [Units.val_inv_eq_inv_val]; field_simp; ring
  rw [heq, map_mul, Valuation.map_neg, map_inv₀, h.valuation_eq_one h𝔣 v hv, inv_one, one_mul]
  exact h.1 v hv

variable (K 𝔣)

private theorem exists_isRayUnit_of_mem_narrowRaySubgroup (h𝔣 : 𝔣 ≠ ⊥) {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ}
    (hI : I ∈ narrowRaySubgroup K 𝔣) : ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β := by
  refine Subgroup.closure_induction (p := fun I _ => ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β)
    ?_ ?_ ?_ ?_ hI
  · rintro I ⟨α, hα0, hα𝔣, hpos, hIα⟩
    have hα0' : (algebraMap (𝓞 K) K α) ≠ 0 := fun h => hα0 ((map_eq_zero_iff _ (RingOfIntegers.coe_injective)).mp h)
    refine ⟨Units.mk0 _ hα0', ⟨fun v hv => ?_, fun τ => hpos τ⟩, Units.ext ?_⟩
    · rw [Units.val_mk0, show algebraMap (𝓞 K) K α - 1 = algebraMap (𝓞 K) K (α - 1) by rw [map_sub, map_one],
        HeightOneSpectrum.valuation_of_algebraMap]
      refine (v.intValuation_le_pow_iff_dvd (α - 1) _).mpr
        (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hα𝔣))))
      have h𝔣0 : (Associates.mk 𝔣) ≠ 0 := Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
      have hirr := Associates.irreducible_mk.mpr v.irreducible
      have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr (k := idealMultiplicity K v 𝔣)).mpr le_rfl
      rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this
    · rw [hIα, coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]
  · exact ⟨1, isRayUnit_one, by rw [map_one]⟩
  · rintro I J _ _ ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
    exact ⟨β * β', hβ.mul h𝔣 hβ', by rw [map_mul]⟩
  · rintro I _ ⟨β, hβ, rfl⟩
    exact ⟨β⁻¹, hβ.inv h𝔣, by rw [map_inv]⟩

end RayUnit
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section UnitIdeles

variable (𝔣 : Ideal (𝓞 K))

private theorem adele_snd_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v := by
  rw [projFin_val]

variable {K 𝔣}

variable (K 𝔣)

private theorem isAdjuster_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) : IsAdjuster K 𝔣 u 1 := by
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · rw [map_one, inv_one, mul_one, adele_snd_apply]
    exact ⟨hu.1 v, hu.2.1 v hv⟩
  · rw [map_one, inv_one, mul_one]; exact hu.2.2 τ

private theorem fadContentHom_projFin_eq_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) :
    fadContentHom K (projFin K u) = 1 := by
  rw [fadContentHom_apply]
  exact finprod_eq_one_of_forall_eq_one fun v => by rw [(placeOrd_eq_zero_iff K _ v).mpr (hu.1 v), zpow_zero]

private theorem unitIdeles_le_ker (h𝔣 : 𝔣 ≠ ⊥) : unitIdeles K 𝔣 ≤ (ideleContentHom K 𝔣).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 (isAdjuster_one_of_mem_unitIdeles K 𝔣 hu)]
  refine NarrowRayClassGroup.mk_eq_one_of_mem K ?_
  have h1 : fadContentHom K (projFin K (u * (pK 1)⁻¹)) = 1 := by
    rw [map_one, inv_one, mul_one]; exact fadContentHom_projFin_eq_one_of_mem_unitIdeles K 𝔣 hu
  show fadContentHom K (projFin K (u * (pK 1)⁻¹)) ∈ narrowRaySubgroup K 𝔣
  rw [h1]; exact one_mem _

private theorem principalIdeles_le_ker : principalIdeles K ≤ (ideleContentHom K 𝔣).ker := by
  rintro _ ⟨α, rfl⟩
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end UnitIdeles
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section Ker

variable (𝔣 : Ideal (𝓞 K))

private theorem coe_sub_one_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (((x - 1 : K)) : v.adicCompletion K) = (x : v.adicCompletion K) - 1 := by
  have h := map_sub (algebraMap K (v.adicCompletion K)) x 1
  rw [map_one] at h
  exact h

private theorem valued_eq_of_fadContentHom_eq {X Y : (FiniteAdeleRing (𝓞 K) K)ˣ} (h : fadContentHom K X = fadContentHom K Y)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((X : FiniteAdeleRing (𝓞 K) K) v) = Valued.v ((Y : FiniteAdeleRing (𝓞 K) K) v) := by
  have hc := congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ => FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) h
  simp only [count_fadContentHom] at hc
  unfold placeOrd at hc
  rw [neg_inj] at hc
  rw [← exp_log (valued_ne_zero_of_unit K X v), ← exp_log (valued_ne_zero_of_unit K Y v), hc]

private theorem ker_ideleContentHom_eq (h𝔣 : 𝔣 ≠ ⊥) :
    (ideleContentHom K 𝔣).ker = principalIdeles K ⊔ unitIdeles K 𝔣 := by
  refine le_antisymm (fun u hu => ?_) (sup_le (principalIdeles_le_ker K 𝔣) (unitIdeles_le_ker K 𝔣 h𝔣))
  obtain ⟨α, hα⟩ := exists_isAdjuster K h𝔣 u
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 hα, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hu
  obtain ⟨β, hβ, hcβ⟩ := exists_isRayUnit_of_mem_narrowRaySubgroup K 𝔣 h𝔣 hu

  have hcont : fadContentHom K (projFin K (u * (pK α)⁻¹)) = fadContentHom K (projFin K (pK β)) := by
    rw [projFin_principal, fadContentHom_unitEmbedding]; exact hcβ
  set w : (AdeleRing (𝓞 K) K)ˣ := u * (pK α)⁻¹ * (pK β)⁻¹ with hw
  have hw_mem : w ∈ unitIdeles K 𝔣 := by
    have hval : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((projFin K (u * (pK α)⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
          Valued.v (((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) :=
      valued_eq_of_fadContentHom_eq K hcont
    have hβv : ∀ v : HeightOneSpectrum (𝓞 K),
        ((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = ((β : K) : v.adicCompletion K) := by
      intro v; rw [projFin_principal]; rfl
    have hβ1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → Valued.v (((β : K) : v.adicCompletion K)) = 1 := by
      intro v hv; rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hβ.valuation_eq_one h𝔣 v hv
    have hβc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v (((β : K) : v.adicCompletion K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
      intro v hv
      rw [← coe_sub_one_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hβ.1 v hv
    have hβ0 : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((β : K) : v.adicCompletion K)) ≠ 0 := by
      intro v; rw [← hβv]; exact valued_ne_zero_of_unit K _ v
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => ?_⟩
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_mul, map_inv, fad_units_inv_apply, map_inv₀, hval v, hβv,
        mul_inv_cancel₀ (hβ0 v)]
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_inv, fad_units_inv_apply, hβv]
      have hca := (hα.cong v hv).2
      rw [adele_snd_apply] at hca
      exact unit_cong_div K hca (hβ1 v hv) (hβc v hv)
    · rw [hw, archSign_mul, archSign_inv, archSign_principal]
      exact iff_of_true (hα.sign τ) (hβ.2 τ)
  have hu_eq : u = pK (α * β) * w := by
    have hw' : w = (pK β)⁻¹ * ((pK α)⁻¹ * u) := by rw [hw, mul_comm (u * (pK α)⁻¹), mul_comm u]
    rw [hw', map_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_left]
  rw [hu_eq]
  exact Subgroup.mul_mem_sup ⟨α * β, rfl⟩ hw_mem

private theorem ker_ideleContentHom_le_of_unitIdeles_le (h𝔣 : 𝔣 ≠ ⊥) {N : Subgroup (AdeleRing (𝓞 K) K)ˣ}
    (hN : unitIdeles K 𝔣 ≤ N) : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ N := by
  rw [ker_ideleContentHom_eq K 𝔣 h𝔣]; exact sup_le_sup_left hN _

end Ker
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem principalIdeles_eq : principalIdeles K = M4aHerbrand.principalIdeles (𝓞 K) K := rfl

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter WithZero"

open scoped nonZeroDivisors

section Uniformizer

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def unifAt : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_unifAt : Valued.v (unifAt K v) = exp (-1 : ℤ) := by
  unfold unifAt
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem unifAt_ne_zero : unifAt K v ≠ 0 := fun h => by
  have h1 := valued_unifAt K v
  rw [h, map_zero] at h1
  exact exp_ne_zero h1.symm

private theorem isUnit_mulSingle (x : v.adicCompletion K) (hx : x ≠ 0) [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    IsUnit (show FiniteAdeleRing (𝓞 K) K from
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, ?_⟩
  · show Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w ≠ 0
    by_cases h : w = v
    · subst h; rw [Pi.mulSingle_eq_same]; exact hx
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_ne_zero
  · filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) ∈ Filter.cofinite by simp] with w hw
    show Valued.v (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w) = 1
    rw [Pi.mulSingle_eq_of_ne (by simpa using hw), map_one]

open scoped Classical in

private noncomputable def uniformizerFad : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_mulSingle K v (unifAt K v) (unifAt_ne_zero K v)).unit

open scoped Classical in
private theorem uniformizerFad_apply (w : HeightOneSpectrum (𝓞 K)) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
      Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v (unifAt K v) w := by
  unfold uniformizerFad
  rw [IsUnit.unit_spec]
  rfl

open scoped Classical in
private theorem uniformizerFad_apply_self :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = unifAt K v := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_same]

open scoped Classical in
private theorem uniformizerFad_apply_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1 := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_of_ne hw]

private noncomputable def uniformizerIdele : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (uniformizerFad K v : FiniteAdeleRing (𝓞 K) K))
  inv := (1, ((uniformizerFad K v)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ))
  val_inv := Prod.ext (one_mul 1) (uniformizerFad K v).mul_inv
  inv_val := Prod.ext (one_mul 1) (uniformizerFad K v).inv_mul

private theorem uniformizerIdele_snd :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = uniformizerFad K v := rfl

private theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (uniformizerIdele K v) = primeClass K 𝔣 v hv := by
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv (uniformizerIdele K v) rfl (fun w hw => ?_) ?_ (fun w hw𝔣 => ?_)
  · rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hw, map_one]
  · rw [uniformizerIdele_snd, uniformizerFad_apply_self, valued_unifAt]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
    rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hwv, sub_self, map_zero]
    exact zero_le'

end Uniformizer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section Surj

variable (K : Type*) [Field K] [NumberField K]

private theorem ideleContentHom_surjective (𝔣 : Ideal (𝓞 K)) : Function.Surjective (ideleContentHom K 𝔣) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hc : c ∈ (⊤ : Subgroup ↥(coprimeToModulus K 𝔣)) := Subgroup.mem_top c
  rw [← closure_primeCarriers_eq_top K 𝔣] at hc
  refine Subgroup.closure_induction (p := fun c _ => ∃ u, ideleContentHom K 𝔣 u = QuotientGroup.mk' _ c)
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨uniformizerIdele K w, ideleContentHom_uniformizerIdele K w 𝔣 hw⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro a b _ _ ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u * u', by rw [map_mul, map_mul, hu, hu']⟩
  · rintro a _ ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

end Surj
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

open scoped nonZeroDivisors

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_index_eq_of_anchors (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index :=
  normRaySubgroup_index_eq_idele_index K L 𝔣 h𝔣 Nrm hA1 hA2 (ideleContentHom_surjective K 𝔣)
    (ideleContentHom_surjective L (modulusExt K L 𝔣)) (ker_ideleContentHom_le_of_unitIdeles_le K 𝔣 h𝔣 hA3)

variable [IsGalois K L]

private theorem firstInequalityCTM_of_idele (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (principalIdeles K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 := by
  unfold FirstInequalityCTM
  rw [IsGalois.card_aut_eq_finrank, normRaySubgroup_index_eq_of_anchors K L 𝔣 h𝔣 Nrm hA1 hA2 hA3]
  exact hH1d

private theorem firstInequalityCTM_of_idele' (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele K L 𝔣 h𝔣 Nrm hA1 hA2 hA3 (principalIdeles_eq K ▸ hH1d)

private theorem firstInequalityCTM_of_idele_admissible (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : IsAdmissibleModulus K L 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele' K L 𝔣 hadm.1 Nrm hA1 hA2 (hA3 hadm) hH1d

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter IntermediateField"

open scoped nonZeroDivisors IsMulCommutative

section Onto

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem firstInequalityCTM_intermediateField_of_idele (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K))
    (hadm : IsAdmissibleModulus K M 𝔣)
    (Nrm : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 F) F)ˣ} {α : (F)ˣ},
      IsAdjuster F (modulusExt K F 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K F (fadContentHom F (projFin F u)))
    (hA3 : IsAdmissibleModulus K F 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K F ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K F 𝔣 :=
  haveI := isGalois_intermediateField K M F
  firstInequalityCTM_of_idele_admissible K F 𝔣 (hadm.of_intermediateField K M F) Nrm hA1 hA2 hA3 hH1d

end Onto
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

open scoped nonZeroDivisors

section Dock

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem fracRelNormUnit_eq_kummerNorm :
    fracRelNormUnit K L = raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
      primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) := rfl

private theorem range_relNormCTM_eq (𝔣 : Ideal (𝓞 K)) :
    (relNormCTM K L 𝔣).range =
      ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣) := by
  rw [← fracRelNormUnit_eq_kummerNorm]
  ext x
  simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : (FractionalIdeal ((𝓞 L)⁰) L)ˣ), y.2, (coe_relNormCTM K L y).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, Subtype.ext (by rw [coe_relNormCTM]; exact hzx)⟩

private theorem normRaySubgroup_eq_kummer (𝔣 : Ideal (𝓞 K)) :
    normRaySubgroup K L 𝔣 =
      (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
        ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
          primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣) := by
  rw [normRaySubgroup, range_relNormCTM_eq]

private theorem secondInequalityCTM_of_kummer (𝔣 : Ideal (𝓞 K))
    (hH1 : ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
      ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣)).index ∣
      Nat.card (L ≃ₐ[K] L)) :
    SecondInequalityCTM K L 𝔣 := by
  unfold SecondInequalityCTM
  rwa [normRaySubgroup_eq_kummer]

variable [IsGalois K L]

end Dock
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter IntermediateField"

open scoped nonZeroDivisors IsMulCommutative

section Top

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem ideleFirstIneqData_iff_at (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K)) :
    IdeleFirstIneqData K M F 𝔣 ↔ IdeleFirstIneqDataAt K F 𝔣 := Iff.rfl

variable [IsGalois K M]

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem firstInequalityCTM_prime_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣) :
    ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣 := by
  intro F hF
  obtain ⟨Nrm, h1, h2, h3, h4⟩ := hdata F hF
  exact firstInequalityCTM_intermediateField_of_idele K M F 𝔣 hadm Nrm h1 h2 h3 h4

end Top
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply"

open LanglandsTunnell.P2.Artin.Ambient

open scoped IsMulCommutative nonZeroDivisors

section Cross

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {σ : L ≃ₐ[K] L}

private theorem isCyclic_of_pairCore [IsCyclic (L ≃ₐ[K] L)] {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i}
    {cj : ArtinFieldCore K L 𝔣 j} (P : ArtinPairCore K L 𝔣 σ ci cj) : IsCyclic (P.N'' ≃ₐ[P.E''] P.N'') :=
  isCyclic_of_injective (resHom K L P.E'' P.N'') P.hresInj''

private theorem isCyclic_of_core [IsCyclic (L ≃ₐ[K] L)] {i : ↥(primeCarriers K 𝔣)} (c : ArtinFieldCore K L 𝔣 i) :
    IsCyclic (c.N ≃ₐ[c.E] c.N) :=
  isCyclic_of_injective (resHom K L c.E c.N) c.hresInj

end Cross
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

section

set_option autoImplicit false

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField IsDedekindDomain"

open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"

section Generic

private theorem isCyclic_intermediateField {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] [IsCyclic (M ≃ₐ[K] M)]
    (F : IntermediateField K M) : IsCyclic (F ≃ₐ[K] F) := by
  haveI := isGalois_intermediateField (K := K) (M := M) F
  exact isCyclic_of_surjective (AlgEquiv.restrictNormalHom F (K₁ := M))
    (AlgEquiv.restrictNormalHom_surjective M)

private theorem finrank_intermediateField_dvd_twentyFour {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] {m : ℕ} (hm : Nat.card (M ≃ₐ[K] M) = 2 ^ m)
    (F : IntermediateField K M) (hprime : (Module.finrank K F).Prime) :
    Module.finrank K F ∣ 24 := by
  have hdvd : Module.finrank K F ∣ 2 ^ m := by
    rw [← hm, IsGalois.card_aut_eq_finrank]
    exact ⟨Module.finrank F M, (Module.finrank_mul_finrank K F M).symm⟩
  have h2 : Module.finrank K F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
  exact h2 ▸ (by decide : (2 : ℕ) ∣ 24)

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Artin.exists_artinFieldCore_nonempty_artinPairCore Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore"
namespace P2
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove under_primeAbove finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section ATD3Group

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

private theorem atd3_card_gal (h3 : Module.finrank K L = 3) : Nat.card (L ≃ₐ[K] L) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, h3]

private theorem atd3_hexp (h3 : Module.finrank K L = 3) (x : L ≃ₐ[K] L) : x ^ (3 ^ 1) = 1 := by
  rw [pow_one, ← atd3_card_gal h3]
  exact pow_card_eq_one'

end ATD3Group
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section ATD3Generic

private theorem atd3_finrank_intermediateField_dvd_twentyFour {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] (hcard : Nat.card (M ≃ₐ[K] M) ∣ 3)
    (F : IntermediateField K M) : Module.finrank K F ∣ 24 := by
  have hdvd : Module.finrank K F ∣ 3 := by
    refine dvd_trans ?_ hcard
    rw [IsGalois.card_aut_eq_finrank]
    exact ⟨Module.finrank F M, (Module.finrank_mul_finrank K F M).symm⟩
  exact dvd_trans hdvd (by decide : (3 : ℕ) ∣ 24)

end ATD3Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

section ATD3Glue

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

private theorem atd3_card_core_dvd (h3 : Module.finrank K L = 3) {𝔣 : Ideal (𝓞 K)}
    {i : ↥(primeCarriers K 𝔣)} (c : ArtinFieldCore K L 𝔣 i) :
    Nat.card (c.N ≃ₐ[c.E] c.N) ∣ 3 := by
  have hdvd := Subgroup.card_dvd_of_injective _ c.hresInj
  rwa [atd3_card_gal h3] at hdvd

private theorem atd3_card_pairCore_dvd (h3 : Module.finrank K L = 3) {𝔣 : Ideal (𝓞 K)}
    {σ : L ≃ₐ[K] L} {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i} {cj : ArtinFieldCore K L 𝔣 j}
    (P : ArtinPairCore K L 𝔣 σ ci cj) :
    Nat.card (P.N'' ≃ₐ[P.E''] P.N'') ∣ 3 := by
  have hdvd := Subgroup.card_dvd_of_injective _ P.hresInj''
  rwa [atd3_card_gal h3] at hdvd

private theorem atd3_hCSb (h3 : Module.finrank K L = 3) {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i) : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (atd3_card_core_dvd h3 c) with h1 | hc3
  · exact secondInequalityCTM_of_kummer c.E c.N _
      (M4aKummer.normClassIndex_dvd_card_aut c.E c.N 0 (by rw [h1, pow_zero]) _)
  · have hdeg : Module.finrank c.E c.N = 3 := by
      rw [← IsGalois.card_aut_eq_finrank]
      exact hc3
    exact NumberField.PrimeNormIndex.secondInequalityCTM_of_finrank_eq_three c.E c.N hdeg _

private theorem atd3_hFI (h3 : Module.finrank K L = 3) {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i) :
    ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime →
      FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd3_card_gal h3)
  refine firstInequalityCTM_prime_of_ideleData c.E c.N _ c.hadm ?_
  intro F _hprime
  haveI := isCyclic_of_core c
  haveI := isGalois_intermediateField (K := c.E) (M := c.N) F
  haveI := isCyclic_intermediateField (K := c.E) (M := c.N) F
  exact (ideleFirstIneqData_iff_at c.E c.N F _).mpr
    (HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic c.E F
      (atd3_finrank_intermediateField_dvd_twentyFour (atd3_card_core_dvd h3 c) F) _)

private theorem atd3_hdata_pair (h3 : Module.finrank K L = 3) {𝔣 : Ideal (𝓞 K)} {σ : L ≃ₐ[K] L}
    {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i} {cj : ArtinFieldCore K L 𝔣 j}
    (P : ArtinPairCore K L 𝔣 σ ci cj) :
    ∀ F : IntermediateField P.E'' P.N'', (Module.finrank P.E'' F).Prime →
      IdeleFirstIneqData P.E'' P.N'' F (modulusExt K P.E'' P.𝔪'') := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd3_card_gal h3)
  intro F _hprime
  haveI := isCyclic_of_pairCore P
  haveI := isGalois_intermediateField (K := P.E'') (M := P.N'') F
  haveI := isCyclic_intermediateField (K := P.E'') (M := P.N'') F
  exact (ideleFirstIneqData_iff_at P.E'' P.N'' F _).mpr
    (HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic P.E'' F
      (atd3_finrank_intermediateField_dvd_twentyFour (atd3_card_pairCore_dvd h3 P) F) _)

end ATD3Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.NumberField Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.Deep.NTSupply"
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three.LanglandsTunnell.P2.Artin"

universe u v

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (h3 : Module.finrank K L = 3) (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) :
    ∃ (σ : L ≃ₐ[K] L) (Ip : Type (max u v)) (_ : CommGroup Ip)
      (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣)))
      (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
      (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ),
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ normRaySubgroup K L 𝔣) ∧
      (∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣,
        ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd3_card_gal h3)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)

  obtain ⟨D, hP⟩ := LanglandsTunnell.Artin.exists_artinFieldCore_nonempty_artinPairCore K L 3 1
    Nat.prime_three (atd3_hexp h3) 𝔣 hadm σ
  have hcross : ∀ i j : ↥(primeCarriers K 𝔣),
      ∃ (b : (D i).Ip) (b' : (D j).Ip), (D i).Ni b = (D j).Ni b' ∧ (D i).ωpi b = σ :=
    LanglandsTunnell.Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore D (fun i j => (hP i j).some)
      (fun i j => atd3_hdata_pair h3 (hP i j).some)

  let N' : ↥(coprimeToModulus K 𝔣) → ((∀ i, (D i).Ip) →* ↥(coprimeToModulus K 𝔣)) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then (D ⟨p, hp⟩).Ni.comp (Pi.evalMonoidHom (fun i => (D i).Ip) ⟨p, hp⟩) else 1
  let ω' : ↥(coprimeToModulus K 𝔣) → ((∀ i, (D i).Ip) →* (L ≃ₐ[K] L)) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then (D ⟨p, hp⟩).ωpi.comp (Pi.evalMonoidHom (fun i => (D i).Ip) ⟨p, hp⟩) else 1
  let P' : ↥(coprimeToModulus K 𝔣) → (∀ i, (D i).Ip) := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then Pi.mulSingle (⟨p, hp⟩ : ↥(primeCarriers K 𝔣)) (D ⟨p, hp⟩).Pi else 1
  let d' : ↥(coprimeToModulus K 𝔣) → ℤ := fun p =>
    if hp : p ∈ primeCarriers K 𝔣 then
      (Subgroup.mem_zpowers_iff.mp (hσ (artinFrob K L (D ⟨p, hp⟩).v))).choose else 0
  refine ⟨σ, ∀ i, (D i).Ip, inferInstance, N', ω', P', d', ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp x
    simp only [N', ω', dif_pos hp, MonoidHom.comp_apply]
    exact hcompat_of_core (D ⟨p, hp⟩) _
  · intro p hp x hx
    simp only [N', ω', dif_pos hp, MonoidHom.comp_apply] at hx ⊢
    exact LanglandsTunnell.Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one (D ⟨p, hp⟩) (atd3_hCSb h3 _)
      (atd3_hFI h3 _) _ hx
  · intro p hp
    simp only [N', P', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
    exact hNP_of_core (D ⟨p, hp⟩)
  · intro p hp
    simp only [ω', P', d', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
    exact hd_zpow_of_core (D ⟨p, hp⟩) hσ
  · intro p hp q hq
    obtain ⟨b, b', hN, hω⟩ := hcross ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨Pi.mulSingle (⟨p, hp⟩ : ↥(primeCarriers K 𝔣)) b, Pi.mulSingle (⟨q, hq⟩ : ↥(primeCarriers K 𝔣)) b', ?_, ?_⟩
    · simp only [N', dif_pos hp, dif_pos hq, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
      exact hN
    · simp only [ω', dif_pos hp, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]
      exact hω

end S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three
end P2MW
export P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_three (solution)
