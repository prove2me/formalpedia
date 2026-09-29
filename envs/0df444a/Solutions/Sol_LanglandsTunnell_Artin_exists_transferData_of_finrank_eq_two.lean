-- Prove2me | solution 1 for LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/950ac1f9-afc2-58aa-8253-94d5b7b42b5e

import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_HeckeCharacter_FiniteOrder
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Index
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_Lift48
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_LanglandsTunnell_C8Character
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Theorems.Thm_HeckeCharacter_ideleFirstIneqDataAt_of_isCyclic
import Theorems.Thm_M4aKummer_normClassIndex_dvd_card_aut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

namespace Deep
namespace NTSupply
p2m_export "Deep.NTSupply" "coprimeToModulus mem_coprimeToModulus_iff mem_narrowRaySet_iff narrowRaySubgroup count_span_singleton_eq_zero_of_sub_one_mem narrowRaySubgroup_le_coprimeToModulus NarrowRayClassGroup NarrowRayClassGroup.mk raySymbol hasFiniteMulSupport_raySymbol_factors raySymbolUnitsHom raySymbolHom raySymbolHom_apply NarrowRayClassGroup.mk_eq_one_of_mem NarrowRayClassGroup.mk_eq_mk_iff mul_mem_narrowRaySet_of_sameSign principalUnit principalUnit_val movingLemma principalUnit_mem_coprimeToModulus finite primeUnit primeUnit_val primeUnit_mem_coprimeToModulus primeClass raySymbol_primeUnit raySymbolDescend raySymbolDescend_mk"
p2m_open "Deep.NTSupply Deep"
end Deep.NTSupply
namespace HeckeCharacter
p2m_export "HeckeCharacter" "placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster idealMultiplicity ideleFirstIneqDataAt_of_isCyclic"
p2m_open "HeckeCharacter"
end HeckeCharacter
namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin
namespace LanglandsTunnell
namespace P0
p2m_open "LanglandsTunnell"
end LanglandsTunnell.P0
namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
p2m_open "LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2
namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Ambient
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"
end LanglandsTunnell.P2.Artin.Ambient

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply WithZero"
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

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
end

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply WithZero"
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

private theorem adj_adele_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK K (α * α'))⁻¹ = (u * (pK K α)⁻¹) * (u' * (pK K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _

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

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain AbsoluteValue"
open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace ComplexEmbedding.isReal_iff InfinitePlace.mk_embedding FinitePlace.norm_lt_one_iff_mem FinitePlace.mk InfinitePlace.embedding_of_isReal_apply RingOfIntegers.mapRingHom InfinitePlace.IsReal InfinitePlace.map_natCast discr of_module_finite mk InfinitePlace.mk_eq_iff InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal RingOfIntegers.not_isField InfinitePlace.mk AdeleRing.algebraMap_fst_apply InfinitePlace.Completion linearDisjoint_of_isGalois_isCoprime_discr FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal InfinitePlace.eq_iff_isEquiv RingOfIntegers RingOfIntegers.ker_algebraMap_eq_bot of_intermediateField RingOfIntegers.basis RingOfIntegers.coe_injective HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace.isReal_iff InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace ComplexEmbedding.conjugate AdeleRing discr_ne_zero FinitePlace.embedding_apply discr_eq_discr_of_algEquiv InfinitePlace.mk_conjugate_eq InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply RingOfIntegers.ext FinitePlace.embedding ComplexEmbedding.conjugate_coe_eq"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem mk_eq_iff pos_iff norm_embedding embedding_apply embedding" end FinitePlace
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

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "mk_embedding embedding_of_isReal_apply IsReal smul_apply mk_eq_iff Completion.extensionEmbeddingOfIsReal_coe embedding_mk_eq_of_isReal mk Completion embedding_of_isReal eq_iff_isEquiv ext comap pos_iff isReal_iff apply embedding mk_conjugate_eq Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply le_iff_le" end InfinitePlace
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

section Battery
p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField"
end Battery
end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
end

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply WithZero"
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

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
end

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"

section Symbol

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

omit [NumberField M] [Algebra K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem map_raySymbol {N N' : Type*} [CommGroup N] [CommGroup N'] (φ : N →* N') (f : HeightOneSpectrum (𝓞 K) → N)
    (I : FractionalIdeal ((𝓞 K)⁰) K) : φ (raySymbol K f I) = raySymbol K (φ ∘ f) I := by
  unfold raySymbol
  rw [φ.map_finprod (hasFiniteMulSupport_raySymbol_factors K f I)]
  simp only [map_zpow, Function.comp_apply]

variable (M' : Type*) [Field M'] [NumberField M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M']
  [IsMulCommutative (M' ≃ₐ[K] M')]

private theorem restrictNormalHom_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K M' 𝔣 I) = artinSymbol K M 𝔣 I := by
  rw [artinSymbol, artinSymbol, raySymbolHom_apply, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [I.2 v hv, zpow_zero, zpow_zero]
  · rw [Function.comp_apply, restrictNormal_artinFrob K M M' v (hI v hv)]

end Symbol
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open scoped IsMulCommutative nonZeroDivisors

section Finite
variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section RaySymbolAux
variable (K : Type*) [Field K] [NumberField K] {G : Type*} [CommGroup G] (f : HeightOneSpectrum (𝓞 K) → G)

end RaySymbolAux
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

omit [NumberField K] [NumberField M] [NumberField E] [NumberField N] [IsGalois E N] in
private theorem resHom_apply (σ : N ≃ₐ[E] N) : resHom K M E N σ = (σ.restrictScalars K).restrictNormal M := rfl

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem resHom_artinFrob (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal :=
  restrictNormal_artinFrob_eq_pow K M E N v w hwv hI

variable [IsMulCommutative (N ≃ₐ[E] N)]

end Tower
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace M4aP2

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"

variable (K : Type*) [Field K] [NumberField K] (q : ℕ)

private theorem norm_int_cast_eq_one_of_sub_one_mem {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(q : 𝓞 K)}) :
    ((Algebra.norm ℤ α : ℤ) : ZMod q) = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hα
  have hsm : q • γ = γ * (q : 𝓞 K) := by rw [nsmul_eq_mul, mul_comm]
  have hαeq : α = 1 + q • γ := by rw [hsm, hγ]; ring
  let b := RingOfIntegers.basis K
  have h1 : ((Algebra.norm ℤ α : ℤ) : ZMod q)
      = ((Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b α)).det := by
    rw [Algebra.norm_eq_matrix_det b, ← RingHom.map_det]; rfl
  have h0 : (q • (Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b γ)
      : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (ZMod q)) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [h1, hαeq, map_add, map_one, map_nsmul, map_add, map_one, map_nsmul, h0, add_zero,
    Matrix.det_one]

private theorem norm_int_pos_of_totPos {α : 𝓞 K} (h0 : α ≠ 0)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    0 < Algebra.norm ℤ α := by
  classical
  set x : K := algebraMap (𝓞 K) K α with hxdef
  have hx0 : x ≠ 0 := by
    rw [hxdef, map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact h0

  have hper : ∀ w : InfinitePlace K, ∃ r : ℝ, 0 < r ∧
      (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (r : ℂ) := by
    intro w
    have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
        = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
          h.trans (InfinitePlace.mk_embedding w).symm
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
      · rintro (h | h)
        · rw [h, InfinitePlace.mk_embedding]
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    by_cases hw : InfinitePlace.IsReal w
    · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
        NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      refine ⟨(InfinitePlace.embedding_of_isReal hw) x, hpos _, ?_⟩
      rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.prod_singleton, InfinitePlace.embedding_of_isReal_apply hw]
    · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
        intro h
        exact hw (InfinitePlace.isReal_iff.mpr
          (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
      have hval0 : w.embedding x ≠ 0 := by
        rw [← map_zero w.embedding]
        exact fun h => hx0 (w.embedding.injective h)
      refine ⟨Complex.normSq (w.embedding x), Complex.normSq_pos.mpr hval0, ?_⟩
      rw [hfibset, Finset.prod_pair hne,
        NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  choose r hrpos hreq using hper

  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => hreq w, ← Complex.ofReal_prod]

  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  have hQpos : 0 < Algebra.norm ℚ x := by
    have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, r w :=
      Complex.ofReal_inj.mp hofreal
    have hP : 0 < ∏ w : InfinitePlace K, r w :=
      Finset.prod_pos fun w _ => hrpos w
    rw [← Rat.cast_pos (K := ℝ), hreal]
    exact hP

  have hcoe : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int α
  have : (0 : ℚ) < ((Algebra.norm ℤ α : ℤ) : ℚ) := by rw [hcoe]; exact hQpos
  exact_mod_cast this

private theorem absNorm_coprime_of_not_dvd (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
  classical
  haveI hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ :=
    FiniteField.card (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  have habs : Ideal.absNorm v.asIdeal = ringChar (𝓞 K ⧸ v.asIdeal) ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← hcard]
  rw [habs]
  refine Nat.Coprime.pow_left _ ?_
  by_contra hnc
  have hpq : ringChar (𝓞 K ⧸ v.asIdeal) ∣ q := by
    by_contra hdvd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  apply hv
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have hpmem : ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_natCast (Ideal.Quotient.mk v.asIdeal), CharP.cast_eq_zero]
  obtain ⟨t, ht⟩ := hpq
  have hqt : ((q : ℕ) : 𝓞 K)
      = ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) * ((t : ℕ) : 𝓞 K) := by
    rw [← Nat.cast_mul, ← ht]
  rw [SetLike.mem_coe, hqt]
  exact Ideal.mul_mem_right _ _ hpmem

private def normClass (v : HeightOneSpectrum (𝓞 K)) : (ZMod q)ˣ :=
  if h : Nat.Coprime (Ideal.absNorm v.asIdeal) q then ZMod.unitOfCoprime _ h else 1

private theorem normClass_coe (v : HeightOneSpectrum (𝓞 K))
    (h : Nat.Coprime (Ideal.absNorm v.asIdeal) q) :
    ((normClass K q v : (ZMod q)ˣ) : ZMod q) = (Ideal.absNorm v.asIdeal : ZMod q) := by
  rw [normClass, dif_pos h, ZMod.coe_unitOfCoprime]

private theorem raySymbol_normClass_coe {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hcop : I ⊔ Ideal.span {(q : 𝓞 K)} = ⊤) :
    ((raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K) : (ZMod q)ˣ) : ZMod q)
      = (Ideal.absNorm I : ZMod q) := by
  classical
  have hI0 : I ≠ 0 := by simpa using hI
  have hvcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I →
      Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
    intro v hvI
    refine absNorm_coprime_of_not_dvd K q v fun hdvd => ?_
    have h1 : I ≤ v.asIdeal := Ideal.le_of_dvd hvI
    have h2 : Ideal.span {(q : 𝓞 K)} ≤ v.asIdeal := Ideal.le_of_dvd hdvd
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := hcop ▸ sup_le h1 h2
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  have hdvd_of_n : ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 → v.asIdeal ∣ I := by
    intro v hv
    rwa [← Associates.count_ne_zero_iff_dvd hI0 v.irreducible]
  have hfuneq : (fun v : HeightOneSpectrum (𝓞 K) =>
        normClass K q v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K))
      = fun v => normClass K q v
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    rw [FractionalIdeal.count_coe K v hI0, zpow_natCast]
  have hfin := hasFiniteMulSupport_raySymbol_factors K (normClass K q)
    (I : FractionalIdeal ((𝓞 K)⁰) K)
  rw [hfuneq] at hfin
  have hsym : raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [raySymbol, hfuneq]
  have hcoe : ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
          : (ZMod q)ˣ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((normClass K q v : ZMod q))
            ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
            : (ZMod q)ˣ) : ZMod q)
        = Units.coeHom (ZMod q) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      MonoidHom.map_finprod (Units.coeHom (ZMod q)) hfin]
    exact finprod_congr fun v => by
      rw [Units.coeHom_apply, Units.val_pow_eq_pow_val]
  have hval : (fun v : HeightOneSpectrum (𝓞 K) =>
        ((normClass K q v : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = fun v => ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    by_cases hv : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hv, pow_zero, pow_zero]
    · rw [normClass_coe K q v (hvcop v (hdvd_of_n v hv))]
  have hnfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show Ideal.absNorm v.asIdeal
      ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hmfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hcast : ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
        = (Nat.castRingHom (ZMod q)) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            Ideal.absNorm v.asIdeal
              ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      map_finprod (Nat.castRingHom (ZMod q)) hnfin]
    exact finprod_congr fun v => by rw [map_pow]; rfl
  have hnat : (∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = Ideal.absNorm I := by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [map_finprod Ideal.absNorm hmfin]
    refine finprod_congr fun v => ?_
    show Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
      = Ideal.absNorm (v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
    exact (map_pow Ideal.absNorm _ _).symm
  rw [hsym, hcoe, hval, ← hcast, hnat]

private theorem normClassKillsRay {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K (normClass K q)
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα0 hα1 hpos
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  have hα1q : α - 1 ∈ Ideal.span {(q : 𝓞 K)} := Ideal.le_of_dvd hq𝔣 hα1
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : α - (α - 1) = 1 := by ring
    exact h1 ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right hα1q)
  have h1 := raySymbol_normClass_coe K q hspan hcop
  rw [Ideal.absNorm_span_singleton] at h1
  have hpos' : 0 < Algebra.norm ℤ α := norm_int_pos_of_totPos K hα0 hpos
  have hnat : (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod q) = 1 := by
    rw [← Int.cast_natCast (R := ZMod q), Int.natAbs_of_nonneg hpos'.le,
      norm_int_cast_eq_one_of_sub_one_mem K q hα1q]
  rw [hnat] at h1
  exact Units.val_eq_one.mp h1

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField"

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

private scoped instance : Algebra.IsIntegral (𝓞 k) (𝓞 (NCl k E)) :=
  ⟨fun x => IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral x)⟩

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
variable (𝔣 : Ideal (𝓞 K)) (𝔑 : Subgroup ↥(coprimeToModulus K 𝔣)) (σ : L ≃ₐ[K] L)
variable {Ip : Type*} [CommGroup Ip]
  (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣))) (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
  (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

end DefN
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section hcompat

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Onto

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private def NoTotallySplitSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F' : IntermediateField K M, F' ≠ ⊥ →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F' ∧ artinFrob K M v x ≠ x

private theorem artinFrob_mem_range_artinSymbol (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinFrob K M v ∈ (artinSymbol K M 𝔣).range :=
  ⟨primeCarrier K 𝔣 v hv, by rw [primeCarrier, artinSymbol_prime K M hv]⟩

private theorem artinFrob_apply_eq_self_of_mem_fixedField (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    {x : M} (hx : x ∈ fixedField (artinSymbol K M 𝔣).range) : artinFrob K M v x = x :=
  (mem_fixedField_iff _ x).mp hx _ (artinFrob_mem_range_artinSymbol K M 𝔣 hv)

private theorem artinSymbol_surjective (𝔣 : Ideal (𝓞 K)) (h : NoTotallySplitSub K M 𝔣) : Function.Surjective (artinSymbol K M 𝔣) := by
  rw [← MonoidHom.range_eq_top]
  set H := (artinSymbol K M 𝔣).range with hH
  have hbot : fixedField H = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, x, hx, hne'⟩ := h (fixedField H) hne
    exact hne' (artinFrob_apply_eq_self_of_mem_fixedField K M 𝔣 hv hx)
  rw [← fixingSubgroup_fixedField H, hbot, fixingSubgroup_bot]

end Onto
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

private theorem ker_artinSymbol_eq_normRaySubgroup (𝔣 : Ideal (𝓞 K))
    (hle : normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker)
    (h : NoTotallySplitSub K L 𝔣)
    (hCSb : SecondInequalityCTM K L 𝔣) :
    (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  have hGpos : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  haveI : (normRaySubgroup K L 𝔣).FiniteIndex :=
    ⟨fun h0 => absurd (h0 ▸ hCSb) (fun h' => hGpos.ne' (Nat.eq_zero_of_zero_dvd h'))⟩
  have hker_idx : (artinSymbol K L 𝔣).ker.index = Nat.card (L ≃ₐ[K] L) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (artinSymbol_surjective K L 𝔣 h),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
  have heq : (normRaySubgroup K L 𝔣).index = (artinSymbol K L 𝔣).ker.index :=
    le_antisymm (hker_idx ▸ Nat.le_of_dvd hGpos hCSb) (Subgroup.index_antitone hle)
  refine le_antisymm (Subgroup.relIndex_eq_one.mp ?_) hle
  have hmul := Subgroup.relIndex_mul_index hle
  rw [heq] at hmul
  exact (mul_eq_right₀ (hker_idx ▸ hGpos.ne')).mp hmul

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

private theorem normRaySubgroup_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hP_ker : (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ≤ (artinSymbol K L 𝔣).ker)
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker :=
  sup_le hP_ker (relNormCTM_range_le_ker_artinSymbol K L 𝔣 hfrob)

end Pincer
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P5
p2m_open "LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField Ideal NumberField.Ideal FrobeniusDensity Matrix FLT.ExplicitLift"
open LanglandsTunnell.P0
open scoped Pointwise

section GaloisGrain

variable {L : Type*} [Field L] [NumberField L]

end GaloisGrain
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P5
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Hfrob

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

attribute [local instance] Ideal.Quotient.field

private theorem artinFrob_pow_inertiaDeg_eq_one (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥) :
    artinFrob K L v ^ v.asIdeal.inertiaDeg' w.asIdeal = 1 := by

  have hmem : artinFrob K L v ∈ MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v) :=
    (isArithFrobAt_artinFrob K L v).mem_stabilizer
  haveI hwv' : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 L ⧸ primeAbove K L v) :=
    Ideal.finiteQuotientOfFreeOfNeBot (primeAbove K L v) (primeAbove_ne_bot K L v)

  have hcard : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[K] L) (primeAbove K L v))
      = v.asIdeal.inertiaDeg' w.asIdeal := by
    haveI := v.isMaximal; haveI := w.isMaximal
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

private theorem hfrob_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣)
    (w : HeightOneSpectrum (𝓞 L)) (hv : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣) :
    artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1 :=
  artinFrob_placeUnder_pow_inertiaDeg_eq_one K L w
    (inertia_eq_bot_of_isAdmissibleModulus K L h (placeUnder' K L w) hv)

end Hfrob
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative

namespace M4aP2

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

p2m_open "IsDedekindDomain.HeightOneSpectrum~ramificationIdx_ne_zero" in open _root_.NumberField.HeightOneSpectrum in
omit [NumberField M] [IsGalois K M] in

private theorem natCast_notMem_primeAbove (q : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    (q : 𝓞 M) ∉ primeAbove K M v := by
  intro hmem
  apply hq
  have h1 : (q : 𝓞 K) ∈ (primeAbove K M v).under (𝓞 K) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]
    exact hmem
  rw [under_primeAbove] at h1
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact h1

p2m_open "IsDedekindDomain.HeightOneSpectrum~ramificationIdx_ne_zero" in open _root_.NumberField.HeightOneSpectrum in

private theorem artinFrob_primitiveRoot {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    artinFrob K M v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hint : IsIntegral ℤ ζ :=
    ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq0, by
      simp [hζ.pow_eq_one]⟩
  let ζO : 𝓞 M := ⟨ζ, hint⟩
  have hpow : ζO ^ q = 1 := Subtype.coe_injective (by push_cast; exact hζ.pow_eq_one)
  have H : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) (artinFrob K M v)).IsArithFrobAt
      (primeAbove K M v) := isArithFrobAt_artinFrob K M v
  have h2 := H.apply_of_pow_eq_one hpow (natCast_notMem_primeAbove K M q v hq)
  have hcard : Nat.card (𝓞 K ⧸ (primeAbove K M v).under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [under_primeAbove, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at h2
  have h3 := congrArg (algebraMap (𝓞 M) M) h2
  rw [map_pow] at h3
  exact h3

p2m_open "IsDedekindDomain.HeightOneSpectrum~ramificationIdx_ne_zero" in open _root_.NumberField.HeightOneSpectrum in

private theorem autToPow_artinFrob {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    hζ.autToPow K (artinFrob K M v) = normClass K q v := by
  have hact := artinFrob_primitiveRoot K M hζ v hq
  have hcop := absNorm_coprime_of_not_dvd K q v hq
  refine Units.ext ?_
  rw [normClass_coe K q v hcop]
  have hspec := hζ.autToPow_spec K (artinFrob K M v)
  have hordζ : orderOf ζ = q := hζ.eq_orderOf.symm
  have hval : ζ ^ ((Ideal.absNorm v.asIdeal : ZMod q)).val = ζ ^ Ideal.absNorm v.asIdeal := by
    rw [ZMod.val_natCast, ← hordζ]
    exact pow_mod_orderOf ζ _
  have hvals : ((hζ.autToPow K (artinFrob K M v) : ZMod q)).val
      = ((Ideal.absNorm v.asIdeal : ZMod q)).val :=
    hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [hspec, hact]; exact hval.symm)
  exact ZMod.val_injective q hvals

p2m_open "IsDedekindDomain.HeightOneSpectrum~ramificationIdx_ne_zero" in open _root_.NumberField.HeightOneSpectrum in

private theorem autToPow_artinSymbol {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I) = raySymbol K (normClass K q) I.1 := by
  have hunf : artinSymbol K M 𝔣 I = raySymbolHom K 𝔣 (artinFrob K M) I := rfl
  rw [hunf, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hcv : FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = 0
  · rw [hcv, zpow_zero, zpow_zero]
  · have hv𝔣 : ¬ v.asIdeal ∣ 𝔣 := fun hdvd => hcv ((mem_coprimeToModulus_iff K).mp I.2 v hdvd)
    have hvq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)} := fun h => hv𝔣 (h.trans hq𝔣)
    simp only [Function.comp_apply]
    rw [autToPow_artinFrob K M hζ v hvq]

end M4aP2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [IsGalois K L]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
variable {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem autToPow_eq_one_iff (τ : M ≃ₐ[K] M) : hζ.autToPow K τ = 1 ↔ τ ζ = ζ := by
  have key : ∀ v : ℕ, ζ ^ v = ζ ↔ (v : ZMod m) = 1 := fun v => by
    rw [show (ζ ^ v = ζ ↔ ζ ^ v = ζ ^ 1) by rw [pow_one], (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq,
      ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  rw [← hζ.autToPow_spec K τ, key, ZMod.natCast_zmod_val, Units.val_eq_one]

private theorem mem_fixingSubgroup_intermediateField_iff (E : IntermediateField K M) (τ : M ≃ₐ[K] M) :
    τ ∈ E.fixingSubgroup ↔ ∀ x ∈ E, τ x = x :=
  _root_.mem_fixingSubgroup_iff _

private theorem apply_eq_self_iff_mem_fixingSubgroup_adjoin (τ : M ≃ₐ[K] M) : τ ζ = ζ ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, adjoin_simple_le_iff, mem_fixedField_iff]
  constructor
  · intro h g hg
    exact (Subgroup.zpowers_le.mpr (show τ ∈ MulAction.stabilizer (M ≃ₐ[K] M) ζ from h) : _ ≤ _) hg
  · intro h
    exact h τ (Subgroup.mem_zpowers τ)

private noncomputable def galProd : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) × C :=
  (AlgEquiv.restrictNormalHom L).prod (ψ.toMonoidHom.comp (hζ.autToPow K))

private theorem galProd_apply_fst (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = AlgEquiv.restrictNormalHom L τ := rfl

private theorem galProd_apply_snd (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = ψ (hζ.autToPow K τ) := rfl

private theorem galProd_fst_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = 1 ↔ τ ∈ L.fixingSubgroup := by
  rw [galProd_apply_fst, mem_fixingSubgroup_intermediateField_iff]
  exact AlgEquiv.restrictNormal_eq_one_iff L τ

private theorem galProd_snd_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = 1 ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [galProd_apply_snd, EmbeddingLike.map_eq_one_iff, autToPow_eq_one_iff, apply_eq_self_iff_mem_fixingSubgroup_adjoin]

private theorem comap_galProd_prod_bot :
    ((⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C)).comap (galProd L hζ ψ) = K⟮ζ⟯.fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_comap, Subgroup.mem_prod, ← galProd_snd_eq_one_iff L hζ ψ, Subgroup.mem_bot]
  exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩

private theorem galProd_injective (htop : L ⊔ K⟮ζ⟯ = ⊤) : Function.Injective (galProd L hζ ψ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro τ hτ
  rw [MonoidHom.mem_ker, Prod.ext_iff] at hτ
  have h1 : τ ∈ L.fixingSubgroup := (galProd_fst_eq_one_iff L hζ ψ τ).mp hτ.1
  have h2 : τ ∈ K⟮ζ⟯.fixingSubgroup := (galProd_snd_eq_one_iff L hζ ψ τ).mp hτ.2
  have h : τ ∈ (L ⊔ K⟮ζ⟯).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, h2⟩
  rw [htop, mem_fixingSubgroup_intermediateField_iff] at h
  exact Subgroup.mem_bot.mpr (AlgEquiv.ext fun x => h x IntermediateField.mem_top)

private theorem galProd_bijective [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : Function.Bijective (galProd L hζ ψ) := by
  classical
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨galProd_injective L hζ ψ htop, ?_⟩
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hdeg, ← Nat.card_congr ψ.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

private noncomputable def galEquivProd [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : (M ≃ₐ[K] M) ≃* (L ≃ₐ[K] L) × C :=
  MulEquiv.ofBijective (galProd L hζ ψ) (galProd_bijective L hζ ψ htop hdeg)

private theorem galEquivProd_apply [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) (τ : M ≃ₐ[K] M) :
    galEquivProd L hζ ψ htop hdeg τ = galProd L hζ ψ τ := rfl

private noncomputable def auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) : IntermediateField K M :=
  fixedField (H.comap (galProd L hζ ψ))

variable [FiniteDimensional K M]

private theorem fixingSubgroup_auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) :
    (auxField L hζ ψ H).fixingSubgroup = H.comap (galProd L hζ ψ) :=
  fixingSubgroup_fixedField _

private theorem mem_fixingSubgroup_auxField {H : Subgroup ((L ≃ₐ[K] L) × C)} {τ : M ≃ₐ[K] M} (h : galProd L hζ ψ τ ∈ H) :
    τ ∈ (auxField L hζ ψ H).fixingSubgroup := by
  rw [fixingSubgroup_auxField]
  exact h

variable [IsGalois K M]

private theorem auxField_sup_adjoin_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) : auxField L hζ ψ H ⊔ K⟮ζ⟯ = ⊤ := by
  have hfix : (auxField L hζ ψ H ⊔ K⟮ζ⟯).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, fixingSubgroup_auxField, ← comap_galProd_prod_bot L hζ ψ,
      ← Subgroup.comap_inf, hH, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).mpr (galProd_injective L hζ ψ htop)]
  rw [← IsGalois.fixedField_fixingSubgroup (auxField L hζ ψ H ⊔ K⟮ζ⟯), hfix, IntermediateField.fixedField_bot]

private theorem adjoin_auxField_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) :
    IntermediateField.adjoin (auxField L hζ ψ H) ({ζ} : Set M) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_adjoin, restrictScalars_top, adjoin_union, adjoin_self]
  exact auxField_sup_adjoin_eq_top L hζ ψ htop hH

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain IntermediateField Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open scoped nonZeroDivisors IsMulCommutative

section Cyclotomic

variable (K M : Type*) [Field K] [Field M] [Algebra K M]
variable {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)

private theorem eq_one_of_autToPow_eq_one (htop : K⟮ζ⟯ = ⊤) {τ : M ≃ₐ[K] M} (h : hζ.autToPow K τ = 1) : τ = 1 := by
  have hfix : τ ∈ K⟮ζ⟯.fixingSubgroup :=
    (apply_eq_self_iff_mem_fixingSubgroup_adjoin τ).mp ((autToPow_eq_one_iff hζ τ).mp h)
  rw [htop, mem_fixingSubgroup_intermediateField_iff] at hfix
  exact AlgEquiv.ext fun x => hfix x IntermediateField.mem_top

variable [NumberField K] [NumberField M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)]

include hζ in

private theorem artinSymbol_eq_one_of_ray (htop : K⟮ζ⟯ = ⊤) {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (I : ↥(coprimeToModulus K 𝔣)) {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α))
    (hI : ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    artinSymbol K M 𝔣 I = 1 := by
  refine eq_one_of_autToPow_eq_one K M hζ htop ?_
  rw [M4aP2.autToPow_artinSymbol K M hζ hq𝔣 I]
  have h := M4aP2.normClassKillsRay K q hq𝔣 α hα0 hα1 hpos
  rw [← hI] at h
  exact h

end Cyclotomic
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Sub

variable (K F M : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M] [IsGalois K F] [IsGalois K M]
  [IsMulCommutative (F ≃ₐ[K] F)] [IsMulCommutative (M ≃ₐ[K] M)]
variable {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)

include hζ in

private theorem artinSymbol_sub_eq_one_of_ray (htop : K⟮ζ⟯ = ⊤) {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M v).under (𝓞 F)).inertia (F ≃ₐ[K] F) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α))
    (hI : ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) :
    artinSymbol K F 𝔣 I = 1 := by
  rw [← restrictNormalHom_artinSymbol K F M 𝔣 hunr I, artinSymbol_eq_one_of_ray K M hζ htop hq𝔣 I hα0 hα1 hpos hI, map_one]

end Sub
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Group

variable {G : Type*} [CommGroup G] [Finite G]

private theorem isSimpleGroup_quotient_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : IsSimpleGroup (G ⧸ H) := by
  haveI : Nontrivial (G ⧸ H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index]
    exact Subgroup.one_lt_index_of_ne_top hH.1
  refine ⟨fun N _ => ?_⟩
  have hle : H ≤ N.comap (QuotientGroup.mk' H) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem N
  have hinj := Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
  rcases hH.le_iff.mp hle with htop | heq
  · right
    exact hinj (htop.trans (Subgroup.comap_top _).symm)
  · left
    refine hinj (heq.trans ?_)
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']

private theorem index_prime_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : H.index.Prime := by
  haveI := isSimpleGroup_quotient_of_isCoatom hH
  exact IsSimpleGroup.prime_card

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Field

variable (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem finrank_fixedField_eq_index (H : Subgroup (M ≃ₐ[K] M)) : Module.finrank K (fixedField H) = H.index := by
  have h1 : Module.finrank K (fixedField H) * Module.finrank (fixedField H) M = Module.finrank K M := Module.finrank_mul_finrank K _ M
  rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M] at h1
  have h2 := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

private theorem exists_le_finrank_prime (F' : IntermediateField K M) (hF' : F' ≠ ⊥) :
    ∃ F : IntermediateField K M, F ≤ F' ∧ (Module.finrank K F).Prime := by
  have hne : F'.fixingSubgroup ≠ ⊤ := fun h => hF' (by
    rw [← IsGalois.fixedField_fixingSubgroup F', h, ← IntermediateField.fixingSubgroup_bot, IsGalois.fixedField_fixingSubgroup])
  obtain ⟨Hm, hcoatom, hle⟩ := (eq_top_or_exists_le_coatom F'.fixingSubgroup).resolve_left hne
  refine ⟨fixedField Hm, ?_, ?_⟩
  · calc fixedField Hm ≤ fixedField F'.fixingSubgroup := fixedField_le hle
      _ = F' := IsGalois.fixedField_fixingSubgroup F'
  · rw [finrank_fixedField_eq_index]
    exact index_prime_of_isCoatom hcoatom

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem isGalois_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M) : IsGalois K F := by
  rw [← IsGalois.fixedField_fixingSubgroup F]
  infer_instance

end Field
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Contract

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

private def NoTotallySplitPrimeSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F : IntermediateField K M, (Module.finrank K F).Prime →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F ∧ artinFrob K M v x ≠ x

variable {K M}

private theorem NoTotallySplitPrimeSub.noTotallySplitSub [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitPrimeSub K M 𝔣) :
    NoTotallySplitSub K M 𝔣 := by
  intro F' hF'
  obtain ⟨F, hle, hp⟩ := exists_le_finrank_prime K M F' hF'
  obtain ⟨v, hv, x, hx, hne⟩ := h F hp
  exact ⟨v, hv, x, hle hx, hne⟩

private theorem artinSymbol_surjective_of_prime [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitPrimeSub K M 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective K M 𝔣 h.noTotallySplitSub

end Contract
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain IntermediateField Polynomial"

section FrobProd

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (L : IntermediateField K M) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem galProd_artinFrob_snd (v : HeightOneSpectrum (𝓞 K)) (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) :
    (galProd L hζ ψ (artinFrob K M v)).2 = ψ (M4aP2.normClass K m v) := by
  rw [galProd_apply_snd, M4aP2.autToPow_artinFrob K M hζ v hm]

end FrobProd
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section DegreeOne

attribute [local instance] Ideal.Quotient.field

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (E : IntermediateField K M)

private theorem isMulCommutative_gal_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] : IsMulCommutative (M ≃ₐ[E] M) :=
  ⟨⟨fun a b => by
    have h := IsMulCommutative.is_comm.comm (a.restrictScalars K) (b.restrictScalars K)
    ext x
    exact AlgEquiv.congr_fun h x⟩⟩

variable {E}
variable [NumberField K] [NumberField M] [IsGalois K M]

private theorem card_quot_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  have hpP : (Q.under (𝓞 E)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨hpP.symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hqdef
  have hq1 : 1 < q := Finite.one_lt_card

  have hge : q ≤ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) :=
    Nat.card_le_card_of_injective _ (algebraMap (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))).injective

  have hfix : ∀ a : 𝓞 E, τ • algebraMap (𝓞 E) (𝓞 M) a = algebraMap (𝓞 E) (𝓞 M) a := fun a =>
    RingOfIntegers.ext ((mem_fixingSubgroup_intermediateField_iff E τ).mp hτ _ (a : E).2)
  have hroot : ∀ y : 𝓞 E ⧸ Q.under (𝓞 E), y ^ q = y := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    have h := H (algebraMap (𝓞 E) (𝓞 M) a)
    rw [MulSemiringAction.toAlgHom_apply, hfix] at h
    exact h
  have hle : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ≤ q := by
    letI := Fintype.ofFinite (𝓞 E ⧸ Q.under (𝓞 E))
    have hne : (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ Q.under (𝓞 E))).val ⊆ (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]).roots := by
      intro y _
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, hroot y, sub_self]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rwa [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1, ← Nat.card_eq_fintype_card] at h
  exact le_antisymm hle hge

private theorem inertiaDeg_under_eq_one_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    (Q.under (𝓞 K)).inertiaDeg' (Q.under (𝓞 E)) = 1 := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  have hq1 : 1 < Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := Finite.one_lt_card
  have hcard := card_quot_under_eq_of_fix hτ Q H
  have hpow := Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ Q.under (𝓞 K)) (V := 𝓞 E ⧸ Q.under (𝓞 E))
  rw [hcard] at hpow
  rw [Ideal.inertiaDeg_algebraMap]
  have h1 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ Module.finrank (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))
      = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ 1 := by
    rw [pow_one]; exact hpow.symm
  exact Nat.pow_right_injective hq1 h1

end DegreeOne
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply IntermediateField HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section Under

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem not_dvd_modulusExt_of_under {E : Type*} [Field E] [NumberField E] [Algebra K E]
    {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) : ¬ w.asIdeal ∣ modulusExt K E 𝔣 := fun h => hv (by
  rw [Ideal.dvd_iff_le] at h ⊢
  rw [← hwv]
  exact Ideal.map_le_iff_le_comap.mp h)

variable (M : Type*) [Field M] [NumberField M] [Algebra K M] (F : IntermediateField K M)

private noncomputable def primeUnderIn (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) :=
  ⟨(primeAbove K M v).under (𝓞 F), ((primeAbove_isMaximal K M v).under (𝓞 F)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField ((primeAbove_isMaximal K M v).under (𝓞 F)) (RingOfIntegers.not_isField F)⟩

private theorem primeUnderIn_asIdeal (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal = (primeAbove K M v).under (𝓞 F) := rfl

private theorem primeUnderIn_under (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal.under (𝓞 K) = v.asIdeal := by
  rw [primeUnderIn_asIdeal, Ideal.under_under, under_primeAbove]

end Under
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Split

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K))

private theorem inertiaDeg_primeUnderIn_eq_one (v : HeightOneSpectrum (𝓞 K)) (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    v.asIdeal.inertiaDeg' (primeUnderIn K M F v).asIdeal = 1 := by
  have h := inertiaDeg_under_eq_one_of_fix (E := F) ((mem_fixingSubgroup_iff F _).mpr hfix) (primeAbove K M v)
    (isArithFrobAt_artinFrob K M v)
  rwa [under_primeAbove] at h

private theorem primeCarrier_mem_range_relNormCTM (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) : primeCarrier K 𝔣 v hv ∈ (relNormCTM K F 𝔣).range :=
  ⟨⟨primeUnit F (primeUnderIn K M F v),
      primeUnit_mem_coprimeToModulus F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v))⟩,
    relNormCTM_primeCarrier_of_inertiaDeg_eq_one K F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v)) hv
      (primeUnderIn_under K M F v) (inertiaDeg_primeUnderIn_eq_one K M F v hfix)⟩

private theorem normRaySubgroup_eq_top_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    normRaySubgroup K F 𝔣 = ⊤ := by
  rw [eq_top_iff, ← closure_primeCarriers_eq_top K 𝔣, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  exact Subgroup.mem_sup_right (primeCarrier_mem_range_relNormCTM K M F 𝔣 v hv (hfix v hv))

private theorem index_normRaySubgroup_eq_one_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    (normRaySubgroup K F 𝔣).index = 1 := by
  rw [normRaySubgroup_eq_top_of_fix K M F 𝔣 hfix, Subgroup.index_top]

end Split
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Reduce

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem noTotallySplitPrimeSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitPrimeSub K M 𝔣 := by
  intro F hF
  by_contra hcon
  push Not at hcon
  have h1 := hFI F hF
  unfold FirstInequalityCTM at h1
  rw [index_normRaySubgroup_eq_one_of_fix K M F 𝔣 hcon, Nat.dvd_one] at h1
  haveI := isGalois_intermediateField K M F
  rw [IsGalois.card_aut_eq_finrank] at h1
  exact hF.ne_one h1

private theorem noTotallySplitSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitSub K M 𝔣 :=
  (noTotallySplitPrimeSub_of_firstInequalityCTM 𝔣 hFI).noTotallySplitSub

private theorem artinSymbol_surjective_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective_of_prime (noTotallySplitPrimeSub_of_firstInequalityCTM 𝔣 hFI)

end Reduce
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section HkerA

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

variable (E N Θ : Type*) [Field E] [NumberField E] [Field N] [NumberField N] [Field Θ] [NumberField Θ]
  [Algebra E N] [Algebra E Θ] [Algebra N Θ] [IsScalarTower E N Θ]
  [IsGalois E N] [IsGalois E Θ] [IsMulCommutative (N ≃ₐ[E] N)] [IsMulCommutative (Θ ≃ₐ[E] Θ)]

private theorem ker_artinSymbol_eq_normRaySubgroup_subcyc {q : ℕ} [NeZero q] {ζ : Θ}
    (hζ : IsPrimitiveRoot ζ q) (htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤)
    (𝔣E : Ideal (𝓞 E)) (hq𝔣 : Ideal.span {(q : 𝓞 E)} ∣ 𝔣E)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ 𝔣E →
      ((primeAbove E Θ v).under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥)
    (hadm : IsAdmissibleModulus E N 𝔣E)
    (hCSb : SecondInequalityCTM E N 𝔣E)
    (hFI : ∀ F : IntermediateField E N, (Module.finrank E F).Prime → FirstInequalityCTM E F 𝔣E) :
    (artinSymbol E N 𝔣E).ker = normRaySubgroup E N 𝔣E := by

  have hP_ker : (narrowRaySubgroup E 𝔣E).subgroupOf (coprimeToModulus E 𝔣E)
      ≤ (artinSymbol E N 𝔣E).ker := by
    intro I hI
    have hI' := Subgroup.mem_subgroupOf.mp hI

    have step : artinSymbol E N 𝔣E
        ⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), narrowRaySubgroup_le_coprimeToModulus E 𝔣E hI'⟩ = 1 := by
      refine Subgroup.closure_induction
        (p := fun J hJ =>
          artinSymbol E N 𝔣E ⟨J, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ⟩ = 1)
        ?_ (map_one _) (fun J₁ J₂ hJ₁ hJ₂ ih₁ ih₂ => ?_) (fun J hJ ih => ?_) hI'
      · intro J hJgen
        obtain ⟨α, hα0, hα1, hpos, hJα⟩ := (mem_narrowRaySet_iff E).mp hJgen
        exact artinSymbol_sub_eq_one_of_ray E N Θ hζ htop hq𝔣 hunr _ hα0 hα1 hpos hJα
      · show artinSymbol E N 𝔣E
          ⟨J₁ * J₂, narrowRaySubgroup_le_coprimeToModulus E 𝔣E (mul_mem hJ₁ hJ₂)⟩ = 1
        rw [show (⟨J₁ * J₂, _⟩ : ↥(coprimeToModulus E 𝔣E))
            = ⟨J₁, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ₁⟩
              * ⟨J₂, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ₂⟩ from rfl,
          map_mul, ih₁, ih₂, one_mul]
      · show artinSymbol E N 𝔣E ⟨J⁻¹, narrowRaySubgroup_le_coprimeToModulus E 𝔣E (inv_mem hJ)⟩ = 1
        rw [show (⟨J⁻¹, _⟩ : ↥(coprimeToModulus E 𝔣E))
            = (⟨J, narrowRaySubgroup_le_coprimeToModulus E 𝔣E hJ⟩ : ↥(coprimeToModulus E 𝔣E))⁻¹ from rfl,
          map_inv, ih, inv_one]
    rwa [show (⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E 𝔣E)) = I from rfl,
      ← MonoidHom.mem_ker] at step

  have hfrob := hfrob_of_isAdmissibleModulus E N hadm

  have h := noTotallySplitSub_of_firstInequalityCTM 𝔣E hFI

  exact ker_artinSymbol_eq_normRaySubgroup E N 𝔣E
    (normRaySubgroup_le_ker_artinSymbol E N 𝔣E hP_ker hfrob) h hCSb

end HkerA
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section hd

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section hcross

variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem placeUnder'_placeUnder' (w' : HeightOneSpectrum (𝓞 E')) :
    placeUnder' k E' w' = placeUnder' k E (placeUnder' E E' w') :=
  IsDedekindDomain.HeightOneSpectrum.ext
    (by rw [placeUnder'_asIdeal, placeUnder'_asIdeal, placeUnder'_asIdeal, Ideal.under_under])

private theorem fracRelNormUnit_fracRelNormUnit_primeUnit (w' : HeightOneSpectrum (𝓞 E')) :
    fracRelNormUnit k E (fracRelNormUnit E E' (primeUnit E' w'))
      = fracRelNormUnit k E' (primeUnit E' w') := by
  rw [fracRelNormUnit_primeUnit E E' w' (placeUnder' E E' w') (placeUnder'_asIdeal E E' w').symm,
    map_pow,
    fracRelNormUnit_primeUnit k E (placeUnder' E E' w') (placeUnder' k E (placeUnder' E E' w'))
      (placeUnder'_asIdeal k E _).symm,
    fracRelNormUnit_primeUnit k E' w' (placeUnder' k E' w') (placeUnder'_asIdeal k E' w').symm,
    ← pow_mul, placeUnder'_placeUnder' k E E']
  congr 1
  haveI : (placeUnder' k E (placeUnder' E E' w')).asIdeal.IsMaximal :=
    (placeUnder' k E (placeUnder' E E' w')).isMaximal
  haveI : (placeUnder' E E' w').asIdeal.IsMaximal := (placeUnder' E E' w').isMaximal
  haveI : (placeUnder' E E' w').asIdeal.LiesOver (placeUnder' k E (placeUnder' E E' w')).asIdeal :=
    ⟨(placeUnder'_asIdeal k E _).symm⟩
  haveI : w'.asIdeal.LiesOver (placeUnder' E E' w').asIdeal := ⟨(placeUnder'_asIdeal E E' w').symm⟩
  exact (Ideal.inertiaDeg_algebra_tower (placeUnder' k E (placeUnder' E E' w')).asIdeal
    (placeUnder' E E' w').asIdeal w'.asIdeal).symm

end hcross
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section ModulusCast
p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors
variable (F : Type*) [Field F] [NumberField F]

private theorem coe_modulusExt_cast {𝔠₁ 𝔠₂ : Ideal (𝓞 F)} (h : 𝔠₁ = 𝔠₂)
    (B : ↥(coprimeToModulus F 𝔠₁)) :
    ((h ▸ B : ↥(coprimeToModulus F 𝔠₂)) : (FractionalIdeal ((𝓞 F)⁰) F)ˣ)
      = (B : (FractionalIdeal ((𝓞 F)⁰) F)ˣ) := by subst h; rfl
end ModulusCast
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section hcross2
variable (k E E' : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

private theorem fracRelNormUnit_comp (u : (FractionalIdeal ((𝓞 E')⁰) E')ˣ) :
    fracRelNormUnit k E' u = fracRelNormUnit k E (fracRelNormUnit E E' u) := by
  have hmem : u ∈ coprimeToModulus E' ⊤ := fun v hv =>
    absurd (top_le_iff.mp (Ideal.le_of_dvd hv)) v.isPrime.ne_top
  have h := MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E' ⊤)
    (f := (fracRelNormUnit k E').comp (coprimeToModulus E' ⊤).subtype)
    (g := ((fracRelNormUnit k E).comp (fracRelNormUnit E E')).comp (coprimeToModulus E' ⊤).subtype)
    (by
      rintro _ ⟨w', _, rfl⟩
      exact (fracRelNormUnit_fracRelNormUnit_primeUnit k E E' w').symm)
  exact DFunLike.congr_fun h ⟨u, hmem⟩

omit [NumberField k] [NumberField E] [NumberField E'] in

private theorem modulusExt_modulusExt (𝔠 : Ideal (𝓞 k)) :
    modulusExt k E' 𝔠 = modulusExt E E' (modulusExt k E 𝔠) := by
  unfold modulusExt
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end hcross2
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

section PPlus

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem relNormCTM_narrowRaySubgroup_subgroupOf_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf
      (coprimeToModulus E (modulusExt K E 𝔣))) :
    relNormCTM K E 𝔣 I ∈ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) := by
  have hI' := Subgroup.mem_subgroupOf.mp hI
  have step : (relNormCTM K E 𝔣
      ⟨_, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hI'⟩ : ↥(coprimeToModulus K 𝔣)).1
        ∈ narrowRaySubgroup K 𝔣 := by
    refine Subgroup.closure_induction
      (p := fun J hJ => ((relNormCTM K E 𝔣
          ⟨J, narrowRaySubgroup_le_coprimeToModulus E (modulusExt K E 𝔣) hJ⟩).1
        : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣)
      ?_ ?_ (fun J₁ J₂ hJ₁ hJ₂ ih₁ ih₂ => ?_) (fun J hJ ih => ?_) hI'
    · intro J hJgen
      obtain ⟨α, hα0, hα1, hpos, hJα⟩ := (mem_narrowRaySet_iff E).mp hJgen
      have heq : (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ (Subgroup.subset_closure hJgen)⟩
            : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨principalUnit E α hα0, principalUnit_mem_coprimeToModulus E hα0 hα1⟩ :=
        Subtype.ext (Units.ext (hJα.trans (principalUnit_val E α hα0).symm))
      show ((relNormCTM K E 𝔣 ⟨J, _⟩).1 : _) ∈ _
      rw [heq]
      refine Subgroup.subset_closure ?_
      rw [mem_narrowRaySet_iff, coe_relNormCTM, Subgroup.coe_mk]
      exact ⟨_, intNorm_ne_zero K E hα0, M4aP2.intNorm_sub_one_mem_of_sub_one_mem K E 𝔣 α hα1,
        M4aP2.intNorm_totPos_of_totPos K E α hα0 hpos,
        (congrArg Units.val (fracRelNormUnit_principalUnit' K E α hα0)).trans
          (principalUnit_val K _ (intNorm_ne_zero K E hα0))⟩
    · show ((relNormCTM K E 𝔣
          ⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), narrowRaySubgroup_le_coprimeToModulus E _ (one_mem _)⟩
          ).1 : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈ narrowRaySubgroup K 𝔣
      rw [show (⟨(1 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _))
          = 1 from rfl, map_one]
      exact one_mem _
    · show ((relNormCTM K E 𝔣 ⟨J₁ * J₂, _⟩).1 : _) ∈ _
      rw [show (⟨J₁ * J₂, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = ⟨J₁, narrowRaySubgroup_le_coprimeToModulus E _ hJ₁⟩
            * ⟨J₂, narrowRaySubgroup_le_coprimeToModulus E _ hJ₂⟩ from rfl, map_mul]
      exact mul_mem ih₁ ih₂
    · show ((relNormCTM K E 𝔣 ⟨J⁻¹, _⟩).1 : _) ∈ _
      rw [show (⟨J⁻¹, _⟩ : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
          = (⟨J, narrowRaySubgroup_le_coprimeToModulus E _ hJ⟩ : ↥(coprimeToModulus E _))⁻¹ from rfl,
        map_inv]
      exact inv_mem ih
  rwa [show (⟨(I : (FractionalIdeal ((𝓞 E)⁰) E)ˣ), _⟩ : ↥(coprimeToModulus E _)) = I from rfl,
    ← Subgroup.mem_subgroupOf] at step

end PPlus
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Range

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_range_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ (relNormCTM E N (modulusExt K E 𝔣)).range) :
    relNormCTM K E 𝔣 I ∈ (relNormCTM K L 𝔣).range := by
  obtain ⟨x, hx⟩ := hI

  refine ⟨relNormCTM L N (modulusExt K L 𝔣) ((modulusExt_modulusExt K L N 𝔣) ▸
    ((modulusExt_modulusExt K E N 𝔣).symm ▸ x)), ?_⟩
  apply Subtype.ext
  rw [coe_relNormCTM, coe_relNormCTM, ← hx, coe_relNormCTM, coe_relNormCTM,
    coe_modulusExt_cast N (modulusExt_modulusExt K L N 𝔣),
    coe_modulusExt_cast N (modulusExt_modulusExt K E N 𝔣).symm,
    ← fracRelNormUnit_comp K L N, ← fracRelNormUnit_comp K E N]

end Range
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Main

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]

private theorem relNormCTM_normRaySubgroup_le (𝔣 : Ideal (𝓞 K))
    (I : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hI : I ∈ normRaySubgroup E N (modulusExt K E 𝔣)) :
    relNormCTM K E 𝔣 I ∈ normRaySubgroup K L 𝔣 := by
  unfold normRaySubgroup at hI ⊢
  have key := (Subgroup.map_sup _ _ (relNormCTM K E 𝔣)).symm ▸
    Subgroup.mem_map_of_mem (relNormCTM K E 𝔣) hI
  have hle : Subgroup.map (relNormCTM K E 𝔣)
        ((narrowRaySubgroup E (modulusExt K E 𝔣)).subgroupOf (coprimeToModulus E (modulusExt K E 𝔣)))
      ⊔ Subgroup.map (relNormCTM K E 𝔣) (relNormCTM E N (modulusExt K E 𝔣)).range
      ≤ (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔ (relNormCTM K L 𝔣).range :=
    sup_le_sup
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_narrowRaySubgroup_subgroupOf_le K E 𝔣 z hz)
      (fun y hy => by obtain ⟨z, hz, hzy⟩ := hy
                      exact hzy ▸ relNormCTM_range_le K L E N 𝔣 z hz)
  exact hle key

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

variable (K L E N Θ : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field E] [NumberField E] [Field N] [NumberField N] [Field Θ] [NumberField Θ]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N]
  [IsScalarTower K E N] [IsScalarTower K L N]
  [Algebra E Θ] [Algebra N Θ] [IsScalarTower E N Θ]
  [IsGalois K L] [IsGalois E N] [IsGalois E Θ]
  [IsMulCommutative (N ≃ₐ[E] N)] [IsMulCommutative (Θ ≃ₐ[E] Θ)]

private theorem hker_family_discharge {q : ℕ} [NeZero q] {ζ : Θ}
    (hζ : IsPrimitiveRoot ζ q) (htop : (IntermediateField.adjoin E {ζ} : IntermediateField E Θ) = ⊤)
    (𝔣 : Ideal (𝓞 K)) (hq𝔣 : Ideal.span {(q : 𝓞 E)} ∣ modulusExt K E 𝔣)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 E), ¬ v.asIdeal ∣ modulusExt K E 𝔣 →
      ((primeAbove E Θ v).under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥)
    (hadm : IsAdmissibleModulus E N (modulusExt K E 𝔣))
    (hCSb : SecondInequalityCTM E N (modulusExt K E 𝔣))
    (hFI : ∀ F : IntermediateField E N, (Module.finrank E F).Prime
      → FirstInequalityCTM E F (modulusExt K E 𝔣))
    (hresInj : Function.Injective (resHom K L E N))
    (x : ↥(coprimeToModulus E (modulusExt K E 𝔣)))
    (hx : ((resHom K L E N).comp (artinSymbol E N (modulusExt K E 𝔣))) x = 1) :
    relNormCTM K E 𝔣 x ∈ normRaySubgroup K L 𝔣 := by
  have hx' : artinSymbol E N (modulusExt K E 𝔣) x = 1 := hresInj (by rwa [map_one])
  have hxker : x ∈ normRaySubgroup E N (modulusExt K E 𝔣) := by
    rw [← ker_artinSymbol_eq_normRaySubgroup_subcyc E N Θ hζ htop (modulusExt K E 𝔣) hq𝔣 hunr
      hadm hCSb hFI]
    exact hx'
  exact relNormCTM_normRaySubgroup_le K L E N 𝔣 x hxker

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section Carrier

variable (K : Type*) [Field K] [NumberField K]

@[scoped simp] private theorem coe_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    ((ctmInclusion K h x : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) = (x : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := rfl

private theorem ctmInclusion_primeCarrier {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔪) :
    ctmInclusion K h (primeCarrier K 𝔪 v hv) = primeCarrier K 𝔣 v (fun hv' => hv (dvd_trans hv' h)) := rfl

private theorem narrowRaySubgroup_antitone {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : narrowRaySubgroup K 𝔪 ≤ narrowRaySubgroup K 𝔣 := by
  refine Subgroup.closure_mono ?_
  rintro I ⟨α, hα0, hα1, hpos, hI⟩
  exact ⟨α, hα0, Ideal.le_of_dvd h hα1, hpos, hI⟩

end Carrier
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Symbol

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem artinSymbol_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (x : ↥(coprimeToModulus K 𝔪)) :
    artinSymbol K M 𝔣 (ctmInclusion K h x) = artinSymbol K M 𝔪 x := by
  show raySymbolHom K 𝔣 (artinFrob K M) _ = raySymbolHom K 𝔪 (artinFrob K M) _
  rw [raySymbolHom_apply, raySymbolHom_apply, coe_ctmInclusion]

end Symbol
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Norm

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

private theorem modulusExt_dvd_modulusExt {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) : modulusExt K L 𝔣 ∣ modulusExt K L 𝔪 :=
  Ideal.le_of_dvd h |> Ideal.map_mono |> Ideal.dvd_iff_le.mpr

private theorem relNormCTM_ctmInclusion {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (y : ↥(coprimeToModulus L (modulusExt K L 𝔪))) :
    relNormCTM K L 𝔣 (ctmInclusion L (modulusExt_dvd_modulusExt K L h) y) = ctmInclusion K h (relNormCTM K L 𝔪 y) :=
  Subtype.ext rfl

private theorem map_normRaySubgroup_ctmInclusion_le {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) :
    (normRaySubgroup K L 𝔪).map (ctmInclusion K h) ≤ normRaySubgroup K L 𝔣 := by
  rw [normRaySubgroup, normRaySubgroup, Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact narrowRaySubgroup_antitone K h (Subgroup.mem_subgroupOf.mp hx)
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨ctmInclusion L (modulusExt_dvd_modulusExt K L h) y, relNormCTM_ctmInclusion K L h y⟩

private theorem ctmInclusion_mem_normRaySubgroup {𝔣 𝔪 : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) {x : ↥(coprimeToModulus K 𝔪)}
    (hx : x ∈ normRaySubgroup K L 𝔪) : ctmInclusion K h x ∈ normRaySubgroup K L 𝔣 :=
  map_normRaySubgroup_ctmInclusion_le K L h ⟨x, hx, rfl⟩

end Norm
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply IntermediateField"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

section PerICore

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

private theorem hker_of_core (hCSb : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪))
    (hFI : ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime
      → FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪))
    (x : c.Ip) (hx : c.ωpi x = 1) : c.Ni x ∈ normRaySubgroup K L 𝔣 :=
  ctmInclusion_mem_normRaySubgroup K L c.h𝔪
    (hker_family_discharge K L c.E c.N c.Θ c.hζ c.htop c.𝔪 c.hq𝔪 c.hunr c.hadm hCSb hFI c.hresInj x hx)

end PerICore
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section FinalCore

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

local notation "K'" => (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)

end FinalCore
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section ed19Prints
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end ed19Prints
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section

set_option autoImplicit false

noncomputable section

open IntermediateField IsDedekindDomain Polynomial
open scoped nonZeroDivisors IsMulCommutative

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Ambient
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

private abbrev Ω : Type _ := AlgebraicClosure L

private scoped instance instCharZeroΩ : CharZero (Ω L) :=
  charZero_of_injective_algebraMap (algebraMap L (Ω L)).injective

private scoped instance instIsIntegralKΩ : Algebra.IsIntegral K (Ω L) := by
  have : Algebra.IsIntegral L (Ω L) := Algebra.IsAlgebraic.isIntegral
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  exact Algebra.IsIntegral.trans L

private def L' : IntermediateField K (Ω L) := (IsScalarTower.toAlgHom K L (Ω L)).fieldRange

private def toL' : L ≃ₐ[K] (L' K L) :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L (Ω L))

private scoped instance instFDL' : FiniteDimensional K (L' K L) := (toL' K L).toLinearEquiv.finiteDimensional
private scoped instance instNFL' : NumberField (L' K L) := NumberField.of_module_finite K (L' K L)
private scoped instance instNormalL' : Normal K (L' K L) := .of_algEquiv (toL' K L)
private scoped instance instGaloisL' : IsGalois K (L' K L) where

section Level

variable (m : ℕ) [NeZero m]

private theorem exists_isPrimitiveRoot_Ω : ∃ ζ : Ω L, IsPrimitiveRoot ζ m := by
  have hne : (cyclotomic m (Ω L)).degree ≠ 0 :=
    (degree_cyclotomic_pos m _ (NeZero.pos m)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic m (Ω L)) hne
  haveI : NeZero (m : Ω L) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  exact ⟨ζ, isRoot_cyclotomic_iff.mp hζ⟩

private def ζΩ : Ω L := (exists_isPrimitiveRoot_Ω L m).choose

private theorem isPrimitiveRoot_ζΩ : IsPrimitiveRoot (ζΩ L m) m :=
  (exists_isPrimitiveRoot_Ω L m).choose_spec

private scoped instance instCycExt : IsCyclotomicExtension {m} K
    (IntermediateField.adjoin K {ζΩ L m} : IntermediateField K (Ω L)) :=
  (isPrimitiveRoot_ζΩ L m).intermediateField_adjoin_isCyclotomicExtension K

private scoped instance instFDAdjζ :
    FiniteDimensional K (IntermediateField.adjoin K {ζΩ L m} : IntermediateField K (Ω L)) :=
  IsCyclotomicExtension.finiteDimensional {m} K _

private scoped instance instGaloisAdjζ :
    IsGalois K (IntermediateField.adjoin K {ζΩ L m} : IntermediateField K (Ω L)) :=
  IsCyclotomicExtension.isGalois {m} K _

private def CycM : IntermediateField K (Ω L) := (L' K L) ⊔ IntermediateField.adjoin K {ζΩ L m}

private scoped instance instFDCycM : FiniteDimensional K (CycM K L m) :=
  show FiniteDimensional K (↥((L' K L) ⊔ adjoin K {ζΩ L m})) from
    IntermediateField.finiteDimensional_sup (L' K L) (adjoin K {ζΩ L m})

private scoped instance instNFCycM : NumberField (CycM K L m) := NumberField.of_module_finite K (CycM K L m)

private scoped instance instNormalCycM : Normal K (CycM K L m) :=
  show Normal K (↥((L' K L) ⊔ adjoin K {ζΩ L m})) from inferInstance

private scoped instance instGaloisCycM : IsGalois K (CycM K L m) where

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

end LanglandsTunnell.P2.Artin.Ambient
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2"

section Battery
open LanglandsTunnell.P2.Artin.Ambient
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

open IntermediateField IsDedekindDomain Polynomial
open scoped nonZeroDivisors IsMulCommutative

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Ambient
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section Level

variable (m : ℕ) [NeZero m]

section PartA

private def L'M : IntermediateField K (CycM K L m) :=
  IntermediateField.restrict (show (L' K L) ≤ CycM K L m from le_sup_left)

private def toL'M : L ≃ₐ[K] (L'M K L m) :=
  (toL' K L).trans (IntermediateField.restrict_algEquiv (show (L' K L) ≤ CycM K L m from le_sup_left))

private scoped instance instFDL'M : FiniteDimensional K (L'M K L m) := (toL'M K L m).toLinearEquiv.finiteDimensional
private scoped instance instNFL'M : NumberField (L'M K L m) := NumberField.of_module_finite K (L'M K L m)
private scoped instance instNormalL'M : Normal K (L'M K L m) := .of_algEquiv (toL'M K L m)
private scoped instance instGaloisL'M : IsGalois K (L'M K L m) where

private def ζM : CycM K L m :=
  ⟨ζΩ L m, le_sup_right (a := (L' K L)) (IntermediateField.mem_adjoin_simple_self K (ζΩ L m))⟩

omit [NumberField K] [IsGalois K L] in
@[scoped simp] private theorem val_ζM : ((ζM K L m : CycM K L m) : Ω L) = ζΩ L m := rfl

omit [NumberField K] [IsGalois K L] in
private theorem isPrimitiveRoot_ζM : IsPrimitiveRoot (ζM K L m) m :=
  (isPrimitiveRoot_ζΩ L m).of_map_of_injective (f := (CycM K L m).val)
    (fun _ _ => Subtype.ext)

omit [NumberField K] [IsGalois K L] in

private theorem L'M_sup_adjoin_eq_top :
    (L'M K L m) ⊔ IntermediateField.adjoin K {ζM K L m} = ⊤ := by
  apply IntermediateField.lift_injective (F := CycM K L m)
  rw [IntermediateField.lift_sup]
  show IntermediateField.lift (IntermediateField.restrict _) ⊔ _ = _
  rw [IntermediateField.lift_restrict, IntermediateField.lift_top,
    IntermediateField.lift_adjoin_simple, val_ζM]
  rfl

private def galEquivL'M : ((L'M K L m) ≃ₐ[K] (L'M K L m)) ≃* (L ≃ₐ[K] L) :=
  (toL'M K L m).autCongr.symm

end PartA
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section PartB

variable (E : IntermediateField K (CycM K L m))

omit [NumberField K] [IsGalois K L] in

private theorem restrict_sup_restrict_eq_top :
    IntermediateField.restrict (show L'M K L m ≤ L'M K L m ⊔ E from le_sup_left)
      ⊔ IntermediateField.restrict (show E ≤ L'M K L m ⊔ E from le_sup_right) = ⊤ := by
  apply IntermediateField.lift_injective (F := L'M K L m ⊔ E)
  rw [IntermediateField.lift_sup, IntermediateField.lift_restrict, IntermediateField.lift_restrict,
    IntermediateField.lift_top]

private scoped instance instNFsup : NumberField ↥(L'M K L m ⊔ E) := NumberField.of_module_finite K _
private scoped instance instNFE : NumberField ↥E := NumberField.of_module_finite K _
private scoped instance instAlgEN : Algebra ↥E ↥(L'M K L m ⊔ E) :=
  (IntermediateField.inclusion (le_sup_right (a := L'M K L m))).toAlgebra
set_option synthInstance.maxHeartbeats 800000 in
private scoped instance instSTKEN : IsScalarTower K ↥E ↥(L'M K L m ⊔ E) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
private scoped instance instAlgL'MN : Algebra ↥(L'M K L m) ↥(L'M K L m ⊔ E) :=
  (IntermediateField.inclusion (le_sup_left (b := E))).toAlgebra
set_option synthInstance.maxHeartbeats 800000 in
private scoped instance instSTKLMN : IsScalarTower K ↥(L'M K L m) ↥(L'M K L m ⊔ E) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)

private scoped instance instNormalRestrictL'M :
    Normal K ↥(IntermediateField.restrict (show L'M K L m ≤ L'M K L m ⊔ E from le_sup_left)) :=
  .of_algEquiv (IntermediateField.restrict_algEquiv _)

omit [NumberField K] [IsGalois K L] in

private theorem mem_fixingSubgroup_restrict_of_restrictScalars
    (σ : ↥(L'M K L m ⊔ E) ≃ₐ[↥E] ↥(L'M K L m ⊔ E)) :
    σ.restrictScalars K ∈
      (IntermediateField.restrict (show E ≤ L'M K L m ⊔ E from le_sup_right)).fixingSubgroup := by
  intro ⟨x, hx⟩
  obtain ⟨e, rfl⟩ := AlgHom.mem_fieldRange.mp hx
  exact σ.commutes e

set_option synthInstance.maxHeartbeats 800000 in

private theorem resHom_injective_sup :
    Function.Injective (resHom K ↥(L'M K L m) ↥E ↥(L'M K L m ⊔ E)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ (hσ : resHom K ↥(L'M K L m) ↥E ↥(L'M K L m ⊔ E) σ = 1)
  rw [resHom_apply] at hσ
  have hL : σ.restrictScalars K ∈
      (IntermediateField.restrict
        (show L'M K L m ≤ L'M K L m ⊔ E from le_sup_left)).fixingSubgroup := by
    intro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    have := (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) ↥(L'M K L m) a).symm
    rwa [hσ, AlgEquiv.one_apply] at this
  have hE := mem_fixingSubgroup_restrict_of_restrictScalars K L m E σ
  have h1 : σ.restrictScalars K ∈ (⊤ : IntermediateField K ↥(L'M K L m ⊔ E)).fixingSubgroup := by
    rw [← restrict_sup_restrict_eq_top K L m E, IntermediateField.fixingSubgroup_sup]
    exact ⟨hL, hE⟩
  rw [IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at h1
  exact AlgEquiv.ext fun x => show σ x = x from DFunLike.ext_iff.mp h1 x

end PartB
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin.Ambient
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
open LanglandsTunnell.P2.Artin.Ambient
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

open IntermediateField IsDedekindDomain
open scoped nonZeroDivisors IsMulCommutative

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Ambient
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section Level

variable (m : ℕ) [NeZero m] (E : IntermediateField K (CycM K L m))

private def inclL : L →ₐ[K] ↥(L'M K L m ⊔ E) :=
  (IntermediateField.inclusion (le_sup_left (b := E))).comp (toL'M K L m).toAlgHom

set_option synthInstance.maxHeartbeats 800000 in
private scoped instance instAlgLN : Algebra L ↥(L'M K L m ⊔ E) :=
  (inclL K L m E).toRingHom.toAlgebra

set_option synthInstance.maxHeartbeats 800000 in
private scoped instance instSTKLN : IsScalarTower K L ↥(L'M K L m ⊔ E) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => ((inclL K L m E).commutes x).symm)

set_option synthInstance.maxHeartbeats 800000 in
omit [NumberField K] [IsGalois K L] in
private theorem algebraMap_L_eq_inclusion_toL'M (a : L) :
    algebraMap L ↥(L'M K L m ⊔ E) a
      = IntermediateField.inclusion (le_sup_left (b := E)) (toL'M K L m a) := rfl

set_option synthInstance.maxHeartbeats 800000 in

private theorem resHom_L'M_eq_one_of_resHom_L_eq_one
    (σ : ↥(L'M K L m ⊔ E) ≃ₐ[↥E] ↥(L'M K L m ⊔ E))
    (hσ : resHom K L ↥E ↥(L'M K L m ⊔ E) σ = 1) :
    resHom K ↥(L'M K L m) ↥E ↥(L'M K L m ⊔ E) σ = 1 := by
  rw [resHom_apply] at hσ ⊢
  refine AlgEquiv.ext fun b => ?_
  apply (algebraMap ↥(L'M K L m) ↥(L'M K L m ⊔ E)).injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
  show (σ.restrictScalars K) (IntermediateField.inclusion (le_sup_left (b := E)) b) = _
  obtain ⟨a, rfl⟩ := (toL'M K L m).surjective b
  rw [← algebraMap_L_eq_inclusion_toL'M, ← AlgEquiv.restrictNormal_commutes (E := L),
    hσ, AlgEquiv.one_apply]
  rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in

private theorem resHom_injective_sup_L :
    Function.Injective (resHom K L ↥E ↥(L'M K L m ⊔ E)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  exact resHom_injective_sup K L m E
    ((resHom_L'M_eq_one_of_resHom_L_eq_one K L m E σ hσ).trans (map_one _).symm)

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin.Ambient
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
open LanglandsTunnell.P2.Artin.Ambient
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section Exponent

variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem admissibleExp_le (w' : HeightOneSpectrum (𝓞 E)) (v₀ : HeightOneSpectrum (𝓞 K)) (hwv : w'.asIdeal.under (𝓞 K) = v₀.asIdeal) :
    admissibleExp E w' ≤ Ideal.ramificationIdx' v₀.asIdeal w'.asIdeal * admissibleExp K v₀ := by
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 E)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (RingOfIntegers.ker_algebraMap_eq_bot K E)
  have hmap0 : Ideal.map (algebraMap (𝓞 K) (𝓞 E)) v₀.asIdeal ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr v₀.ne_bot
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 E)) v₀.asIdeal ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.mpr (le_of_eq hwv.symm)
  have he' : Ideal.ramificationIdx' v₀.asIdeal w'.asIdeal ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap0 w'.isPrime hle
  have h2 : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(2 : ℤ)}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot, map_ofNat]
    exact two_ne_zero
  have h3 : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(3 : ℤ)}) ≠ ⊥ := by
    rw [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (algebraMap ℤ (𝓞 E)).injective_int).mpr (by norm_num)
  have htower2 := Ideal.ramificationIdx_algebra_tower (p := Ideal.span {(2 : ℤ)}) (P := v₀.asIdeal) (Q := w'.asIdeal) hmap0 h2 hle
  have htower3 := Ideal.ramificationIdx_algebra_tower (p := Ideal.span {(3 : ℤ)}) (P := v₀.asIdeal) (Q := w'.asIdeal) hmap0 h3 hle
  unfold admissibleExp
  rw [htower2, htower3]
  have h1 : 1 ≤ Ideal.ramificationIdx' v₀.asIdeal w'.asIdeal := Nat.one_le_iff_ne_zero.mpr he'
  nlinarith [h1]

end Exponent
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Descent

variable (K L E N : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra L N] [Algebra E N] [IsScalarTower K L N] [IsScalarTower K E N]
  [IsGalois K L] [IsGalois E N]

omit [NumberField K] [NumberField E] [NumberField L] [NumberField N] [IsGalois E N] in

private theorem resHom_mem_inertia {𝔓 : Ideal (𝓞 N)} {σ : N ≃ₐ[E] N} (hσ : σ ∈ 𝔓.inertia (N ≃ₐ[E] N)) :
    resHom K L E N σ ∈ (𝔓.under (𝓞 L)).inertia (L ≃ₐ[K] L) := by
  intro y
  have h := hσ (algebraMap (𝓞 L) (𝓞 N) y)
  simp only [Submodule.mem_toAddSubgroup, Ideal.under_def, Ideal.mem_comap, map_sub] at h ⊢
  have heq : algebraMap (𝓞 L) (𝓞 N) (resHom K L E N σ • y) = σ • algebraMap (𝓞 L) (𝓞 N) y :=
    RingOfIntegers.ext (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) L (y : L))
  rwa [heq]

omit [NumberField K] [NumberField E] [NumberField L] [NumberField N] [IsGalois E N] in

private theorem inertia_eq_bot_of_resHom_injective (hres : Function.Injective (resHom K L E N)) (𝔓 : Ideal (𝓞 N))
    (hL : (𝔓.under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥) : 𝔓.inertia (N ≃ₐ[E] N) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  apply hres
  rw [map_one]
  have h := resHom_mem_inertia K L E N hσ
  rwa [hL, Subgroup.mem_bot] at h

omit [NumberField K] in

private theorem dvd_modulusExt_of_under_dvd {𝔪 : Ideal (𝓞 K)} {w : Ideal (𝓞 E)} (h : w.under (𝓞 K) ∣ 𝔪) : w ∣ modulusExt K E 𝔪 :=
  Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr (Ideal.le_of_dvd h))

private theorem inertia_eq_bot_of_isAdmissibleModulus_of_not_under_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K L 𝔣)
    (P : Ideal (𝓞 L)) [hPm : P.IsMaximal] (hP : ¬ P.under (𝓞 K) ∣ 𝔣) : P.inertia (L ≃ₐ[K] L) = ⊥ := by
  have hPne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField L)
  let p₀ : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), (hPm.under (𝓞 K)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (hPm.under (𝓞 K)) (RingOfIntegers.not_isField K)⟩
  have hI0 : (primeAbove K L p₀).inertia (L ≃ₐ[K] L) = ⊥ := inertia_eq_bot_of_isAdmissibleModulus K L h𝔣 p₀ hP
  have he : p₀.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    by_contra he
    exact (inertia_ne_bot_iff_ramificationIdxIn_ne_one K L p₀).mpr he hI0
  haveI : P.LiesOver p₀.asIdeal := ⟨rfl⟩
  haveI : p₀.asIdeal.IsMaximal := p₀.isMaximal
  haveI : Finite (𝓞 K ⧸ p₀.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot p₀.asIdeal p₀.ne_bot
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) p₀.asIdeal P
  rwa [he, Subgroup.card_eq_one] at hc

private theorem inertia_primeAbove_ne_bot_of_inertia_ne_bot (P : Ideal (𝓞 L)) [hPm : P.IsMaximal] (v : HeightOneSpectrum (𝓞 K))
    (hv : P.under (𝓞 K) = v.asIdeal) (hI : P.inertia (L ≃ₐ[K] L) ≠ ⊥) : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ := by
  have hPne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField L)
  rw [inertia_ne_bot_iff_ramificationIdxIn_ne_one K L v]
  intro he
  haveI : P.LiesOver v.asIdeal := ⟨hv.symm⟩
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPne
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal P
  rw [he, Subgroup.card_eq_one] at hc
  exact hI hc

omit [NumberField N] [IsGalois E N] in

private theorem hI_E_of_isAdmissibleModulus {𝔣 𝔪 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K L 𝔣) (h𝔪 : 𝔣 ∣ 𝔪)
    (w' : HeightOneSpectrum (𝓞 E)) (hw' : ¬ w'.asIdeal ∣ modulusExt K E 𝔪) :
    ((primeAbove E N w').under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥ := by
  haveI : ((primeAbove E N w').under (𝓞 L)).IsMaximal := (primeAbove_isMaximal E N w').under (𝓞 L)
  refine inertia_eq_bot_of_isAdmissibleModulus_of_not_under_dvd K L h𝔣 _ (fun hd => hw' (dvd_modulusExt_of_under_dvd K E ?_))
  rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), under_primeAbove] at hd
  exact dvd_trans hd h𝔪

variable (Θ : Type*) [Field Θ] [NumberField Θ] [Algebra E Θ] [Algebra N Θ] [IsScalarTower E N Θ]

omit [NumberField N] [IsGalois E N] [NumberField Θ] in

private theorem hunr_of_isAdmissibleModulus {𝔣 𝔪 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K L 𝔣) (h𝔪 : 𝔣 ∣ 𝔪)
    (hres : Function.Injective (resHom K L E N)) (v' : HeightOneSpectrum (𝓞 E)) (hv' : ¬ v'.asIdeal ∣ modulusExt K E 𝔪) :
    ((primeAbove E Θ v').under (𝓞 N)).inertia (N ≃ₐ[E] N) = ⊥ := by
  haveI h1 : ((primeAbove E Θ v').under (𝓞 N)).IsMaximal := (primeAbove_isMaximal E Θ v').under (𝓞 N)
  haveI : (((primeAbove E Θ v').under (𝓞 N)).under (𝓞 L)).IsMaximal := h1.under (𝓞 L)
  refine inertia_eq_bot_of_resHom_injective K L E N hres _
    (inertia_eq_bot_of_isAdmissibleModulus_of_not_under_dvd K L h𝔣 _ (fun hd => hv' (dvd_modulusExt_of_under_dvd K E ?_)))
  rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), Ideal.under_under (A := 𝓞 E) (B := 𝓞 N), under_primeAbove] at hd
  exact dvd_trans hd h𝔪

omit [IsGalois E N] [NumberField N] in

private theorem isAdmissibleModulus_ext {𝔣 𝔪 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K L 𝔣) (h𝔪 : 𝔣 ∣ 𝔪) (h𝔪0 : 𝔪 ≠ ⊥)
    (hres : Function.Injective (resHom K L E N)) : IsAdmissibleModulus E N (modulusExt K E 𝔪) := by
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 E)) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr (RingOfIntegers.ker_algebraMap_eq_bot K E)
  refine ⟨(Ideal.map_eq_bot_iff_of_injective hinj).not.mpr h𝔪0, fun w' hI => ?_⟩

  set 𝔓 : Ideal (𝓞 N) := primeAbove E N w' with h𝔓
  haveI hPL : (𝔓.under (𝓞 L)).IsMaximal := (primeAbove_isMaximal E N w').under (𝓞 L)
  have hL : (𝔓.under (𝓞 L)).inertia (L ≃ₐ[K] L) ≠ ⊥ := fun h => hI (inertia_eq_bot_of_resHom_injective K L E N hres 𝔓 h)

  let v₀ : HeightOneSpectrum (𝓞 K) := ⟨w'.asIdeal.under (𝓞 K), (w'.isMaximal.under (𝓞 K)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField (w'.isMaximal.under (𝓞 K)) (RingOfIntegers.not_isField K)⟩
  have hv₀ : (𝔓.under (𝓞 L)).under (𝓞 K) = v₀.asIdeal := by
    rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), h𝔓, under_primeAbove]
  have hram : (primeAbove K L v₀).inertia (L ≃ₐ[K] L) ≠ ⊥ := inertia_primeAbove_ne_bot_of_inertia_ne_bot K L _ v₀ hv₀ hL

  have hdiv : v₀.asIdeal ^ admissibleExp K v₀ ∣ 𝔪 := dvd_trans (h𝔣.2 v₀ hram) h𝔪
  have hw : w'.asIdeal ^ Ideal.ramificationIdx' v₀.asIdeal w'.asIdeal ∣ modulusExt K E v₀.asIdeal :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx
  have hpow : w'.asIdeal ^ (Ideal.ramificationIdx' v₀.asIdeal w'.asIdeal * admissibleExp K v₀) ∣ modulusExt K E 𝔪 := by
    rw [pow_mul]
    refine dvd_trans (pow_dvd_pow_of_dvd hw _) ?_
    rw [modulusExt, ← Ideal.map_pow]
    exact Ideal.dvd_iff_le.mpr (Ideal.map_mono (Ideal.le_of_dvd hdiv))
  exact dvd_trans (pow_dvd_pow _ (admissibleExp_le K E w' v₀ rfl)) hpow

end Descent
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

namespace ArtinAux

private theorem orderOf_eq_two_pow_of_dvd_pow_add_one {q N k : ℕ} (hq : q.Prime) (hq2 : Odd q)
    (hdvd : q ∣ N ^ (2 ^ k) + 1) :
    orderOf (N : ZMod q) = 2 ^ (k + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (2 < q) := ⟨hq.odd_iff.mp hq2⟩
  have hpow : (N : ZMod q) ^ (2 ^ k) = -1 := by
    have hcast : ((N ^ (2 ^ k) + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ q).mpr hdvd
    push_cast at hcast
    exact eq_neg_of_add_eq_zero_left hcast
  have hdvd8 : orderOf (N : ZMod q) ∣ 2 ^ (k + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_succ, pow_mul, hpow, neg_one_sq]
  have hndvd4 : ¬ orderOf (N : ZMod q) ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, hpow]
    exact ZMod.neg_one_ne_one
  obtain ⟨j, hjle, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd8
  rcases hjle.lt_or_eq with hj | hj
  · exact absurd (hord ▸ Nat.pow_dvd_pow 2 (Nat.lt_succ_iff.mp hj)) hndvd4
  · exact hord.trans (congrArg (2 ^ ·) hj)

private theorem orderOf_eq_eight_of_dvd_pow_four_add_one {q N : ℕ} (hq : q.Prime) (hq2 : Odd q)
    (hdvd : q ∣ N ^ 4 + 1) :
    orderOf (N : ZMod q) = 8 :=
  orderOf_eq_two_pow_of_dvd_pow_add_one (k := 2) hq hq2 hdvd

private theorem eight_dvd_sub_one_of_dvd_pow_four_add_one {q N : ℕ} (hq : q.Prime) (hq2 : Odd q)
    (hdvd : q ∣ N ^ 4 + 1) :
    8 ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hN0 : (N : ZMod q) ≠ 0 := by
    intro h
    have hqN : q ∣ N := (ZMod.natCast_eq_zero_iff N q).mp h
    exact hq.not_dvd_one ((Nat.dvd_add_right (hqN.pow four_ne_zero)).mp hdvd)
  calc (8 : ℕ) = orderOf (N : ZMod q) :=
        (orderOf_eq_eight_of_dvd_pow_four_add_one hq hq2 hdvd).symm
    _ ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hN0

private theorem pow_two_pow_add_one_dvd_pow_two_pow_sub_one {N a b : ℕ} (hab : a < b) :
    N ^ (2 ^ a) + 1 ∣ N ^ (2 ^ b) - 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Nat.zero_pow (Nat.two_pow_pos a)]
  have h1le : 1 ≤ N ^ (2 ^ a) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hN.ne')
  have h1 : N ^ (2 ^ a) + 1 ∣ N ^ (2 ^ (a + 1)) - 1 := by
    refine ⟨N ^ (2 ^ a) - 1, ?_⟩
    have heq : N ^ (2 ^ (a + 1)) = N ^ (2 ^ a) * N ^ (2 ^ a) := by
      rw [← sq, ← pow_mul, ← pow_succ]
    have hmul : (N ^ (2 ^ a) + 1) * (N ^ (2 ^ a) - 1) + 1 = N ^ (2 ^ a) * N ^ (2 ^ a) := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1le
      rw [hm, Nat.add_sub_cancel_left]; ring
    omega
  exact h1.trans (Nat.pow_sub_one_dvd_pow_sub_one N (Nat.pow_dvd_pow 2 hab))

private theorem gcd_pow_two_pow_add_one_dvd_two {N a b : ℕ} (hab : a ≠ b) :
    (N ^ (2 ^ a) + 1).gcd (N ^ (2 ^ b) + 1) ∣ 2 := by
  wlog h : a < b generalizing a b with H
  · rw [Nat.gcd_comm]; exact H hab.symm (hab.lt_or_gt.resolve_left h)
  set d := (N ^ (2 ^ a) + 1).gcd (N ^ (2 ^ b) + 1) with hd
  have hdb : d ∣ N ^ (2 ^ b) + 1 := Nat.gcd_dvd_right _ _
  have hds : d ∣ N ^ (2 ^ b) - 1 :=
    (Nat.gcd_dvd_left _ _).trans (pow_two_pow_add_one_dvd_pow_two_pow_sub_one h)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [hd, Nat.zero_pow (Nat.two_pow_pos a), Nat.zero_pow (Nat.two_pow_pos b), zero_add,
      Nat.gcd_self]
    exact one_dvd 2
  have h1le : 1 ≤ N ^ (2 ^ b) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hN.ne')
  have hd2 : d ∣ 2 := by
    have := Nat.dvd_sub hdb hds
    rwa [show (N ^ (2 ^ b) + 1) - (N ^ (2 ^ b) - 1) = 2 from by omega] at this
  exact hd2

private theorem exists_odd_prime_dvd_pow_two_pow_add_one {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k) :
    ∃ q, q.Prime ∧ Odd q ∧ q ∣ N ^ (2 ^ k) + 1 := by
  have hM2 : 2 < N ^ (2 ^ k) + 1 := by
    calc 2 < 2 ^ (2 ^ k) + 1 := by
            have : 2 ≤ 2 ^ (2 ^ k) := Nat.le_self_pow (Nat.two_pow_pos k).ne' 2
            omega
      _ ≤ N ^ (2 ^ k) + 1 := by gcongr
  rcases Nat.even_or_odd N with hNe | hNo
  · have hodd : Odd (N ^ (2 ^ k) + 1) :=
      (hNe.pow_of_ne_zero (Nat.two_pow_pos k).ne').add_one
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd (by omega : N ^ (2 ^ k) + 1 ≠ 1)
    exact ⟨q, hq, hq.eq_two_or_odd'.resolve_left
      (fun h2 => hodd.not_two_dvd_nat (h2 ▸ hqdvd)), hqdvd⟩
  · have hN2k4 : N ^ (2 ^ k) % 4 = 1 := by
      obtain ⟨m, rfl⟩ := hNo
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      have hsq : (2 * m + 1) ^ 2 % 4 = 1 := by ring_nf; omega
      rw [show 2 ^ (1 + j) = 2 * 2 ^ j from by ring, pow_mul, Nat.pow_mod, hsq,
        Nat.one_pow, Nat.one_mod_eq_one.mpr (by omega)]
    set M := N ^ (2 ^ k) + 1
    have hM4 : M % 4 = 2 := by omega
    have hMdiv2_odd : Odd (M / 2) := by
      rcases Nat.even_or_odd (M / 2) with ⟨c, hc⟩ | ho
      · exact absurd (show M % 4 = 0 from by omega) (by omega)
      · exact ho
    have hMdiv2_ne1 : M / 2 ≠ 1 := fun h => by omega
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hMdiv2_ne1
    refine ⟨q, hq, hq.eq_two_or_odd'.resolve_left
      (fun h2 => hMdiv2_odd.not_two_dvd_nat (h2 ▸ hqdvd)), hqdvd.trans ?_⟩
    exact ⟨2, by omega⟩

private theorem exists_prime_one_mod_eight_notMem (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ q, q.Prime ∧ 8 ∣ q - 1 ∧ q ∉ B := by
  set M := 2 * ∏ p ∈ B, p with hM
  have hprod_pos : 0 < ∏ p ∈ B, p :=
    Finset.prod_pos (fun p hp => (hB p hp).pos)
  have hM2 : 2 ≤ M := Nat.le_mul_of_pos_right 2 hprod_pos
  obtain ⟨q, hq, hqodd, hqdvd⟩ :=
    exists_odd_prime_dvd_pow_two_pow_add_one (k := 2) hM2 one_le_two
  refine ⟨q, hq, eight_dvd_sub_one_of_dvd_pow_four_add_one hq hqodd hqdvd, ?_⟩
  intro hqB
  have hqM : q ∣ M := (Finset.dvd_prod_of_mem _ hqB).mul_left 2
  exact hq.not_dvd_one
    ((Nat.dvd_add_right (Dvd.dvd.pow hqM four_ne_zero)).mp hqdvd)

private theorem exists_prime_eight_dvd_order_notMem {N : ℕ} (hN : 2 ≤ N) (B : Finset ℕ) :
    ∃ q, q.Prime ∧ q ∉ B ∧ 8 ∣ orderOf (N : ZMod q) := by
  classical
  choose q hqp hqo hqd using
    fun k : ℕ => exists_odd_prime_dvd_pow_two_pow_add_one (k := k + 2) hN (by omega)
  have hq_inj : Function.Injective q := by
    intro j k hjk
    by_contra hne
    have h2 : q j ∣ 2 :=
      (Nat.dvd_gcd (hqd j) (hjk ▸ hqd k)).trans
        (gcd_pow_two_pow_add_one_dvd_two (N := N) (by omega : j + 2 ≠ k + 2))
    have heq2 : q j = 2 := Nat.le_antisymm (Nat.le_of_dvd two_pos h2) (hqp j).two_le
    exact absurd (heq2 ▸ hqo j) (by decide)
  have hcard : B.card < ((Finset.range (B.card + 1)).image q).card := by
    rw [Finset.card_image_of_injective _ hq_inj, Finset.card_range]; omega
  obtain ⟨_, hqs_mem, hqs_notB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hqs_mem
  refine ⟨q k, hqp k, hqs_notB, ?_⟩
  rw [orderOf_eq_two_pow_of_dvd_pow_add_one (hqp k) (hqo k) (hqd k)]
  exact ⟨2 ^ k, by ring⟩

end ArtinAux
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
open ArtinAux
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

private noncomputable def unitGen (p : ℕ) [Fact p.Prime] : (ZMod p)ˣ :=
  Classical.choose (IsCyclic.exists_generator (α := (ZMod p)ˣ))

private theorem unitGen_generates (p : ℕ) [Fact p.Prime] : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers (unitGen p) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := (ZMod p)ˣ))

private theorem orderOf_unitGen (p : ℕ) [Fact p.Prime] : orderOf (unitGen p) = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (unitGen_generates p), Nat.card_eq_fintype_card, ZMod.card_units]

private theorem eight_dvd_orderOf_unitGen (p : ℕ) [Fact p.Prime] (h8 : 8 ∣ p - 1) : 8 ∣ orderOf (unitGen p) := by
  rwa [orderOf_unitGen]

private theorem exists_globalPair (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) :
    ∃ Q Q' : ℕ, Q.Prime ∧ Q'.Prime ∧ Q ∉ B₀ ∧ Q' ∉ B₀ ∧ Q ≠ Q' ∧ 8 ∣ Q - 1 ∧ 8 ∣ Q' - 1 := by
  classical
  obtain ⟨Q, hQ, hQ8, hQB⟩ := ArtinAux.exists_prime_one_mod_eight_notMem B₀ hB₀
  have hB₁ : ∀ p ∈ insert Q B₀, p.Prime := fun p hp => by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hQ
    · exact hB₀ p hp
  obtain ⟨Q', hQ', hQ'8, hQ'B⟩ := ArtinAux.exists_prime_one_mod_eight_notMem (insert Q B₀) hB₁
  refine ⟨Q, Q', hQ, hQ', hQB, fun h => hQ'B (Finset.mem_insert_of_mem h), fun h => hQ'B (h ▸ Finset.mem_insert_self Q B₀), hQ8, hQ'8⟩

private theorem exists_firstPrime {N : ℕ} (hN : 2 ≤ N) (B : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ B ∧ ¬ q ∣ N ∧ 8 ∣ orderOf (N : ZMod q) := by
  classical
  obtain ⟨q, hq, hqB, hq8⟩ := ArtinAux.exists_prime_eight_dvd_order_notMem hN (B ∪ N.primeFactors)
  refine ⟨q, hq, fun h => hqB (Finset.mem_union_left _ h), fun hdvd => hqB (Finset.mem_union_right _ ?_), hq8⟩
  exact Nat.mem_primeFactors.mpr ⟨hq, hdvd, by omega⟩

private theorem coprime_of_prime_not_dvd {N q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) : N.Coprime q :=
  (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN)

private theorem eight_dvd_orderOf_unitOfCoprime {N q : ℕ} (h : N.Coprime q) (h8 : 8 ∣ orderOf (N : ZMod q)) :
    8 ∣ orderOf (ZMod.unitOfCoprime N h) := by
  rwa [← orderOf_units, ZMod.coe_unitOfCoprime]

private theorem exists_firstPrime_unit {N : ℕ} (hN : 2 ≤ N) (B : Finset ℕ) :
    ∃ (q : ℕ) (h : N.Coprime q), q.Prime ∧ q ∉ B ∧ 8 ∣ orderOf (ZMod.unitOfCoprime N h) := by
  obtain ⟨q, hq, hqB, hqN, hq8⟩ := exists_firstPrime hN B
  exact ⟨q, coprime_of_prime_not_dvd hq hqN, hq, hqB, eight_dvd_orderOf_unitOfCoprime _ hq8⟩

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem exists_place_of_primeCarriers (i : ↥(primeCarriers K 𝔣)) :
    ∃ v : HeightOneSpectrum (𝓞 K), ∃ hv : ¬ v.asIdeal ∣ 𝔣, primeCarrier K 𝔣 v hv = i := by
  obtain ⟨v, hv, h⟩ := i.2
  exact ⟨v, hv, h.symm⟩

private noncomputable def carrierPlace (i : ↥(primeCarriers K 𝔣)) : HeightOneSpectrum (𝓞 K) :=
  (exists_place_of_primeCarriers K 𝔣 i).choose

private theorem carrierPlace_not_dvd (i : ↥(primeCarriers K 𝔣)) : ¬ (carrierPlace K 𝔣 i).asIdeal ∣ 𝔣 :=
  (exists_place_of_primeCarriers K 𝔣 i).choose_spec.choose

private theorem primeCarrier_carrierPlace (i : ↥(primeCarriers K 𝔣)) :
    primeCarrier K 𝔣 (carrierPlace K 𝔣 i) (carrierPlace_not_dvd K 𝔣 i) = i :=
  (exists_place_of_primeCarriers K 𝔣 i).choose_spec.choose_spec

private noncomputable def resChar (v : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ v.asIdeal)

omit [NumberField K] in
private theorem natCast_mem_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) : (n : 𝓞 K) ∈ v.asIdeal ↔ resChar K v ∣ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, resChar, ringChar.spec]

private theorem finite_quot (v : HeightOneSpectrum (𝓞 K)) : Finite (𝓞 K ⧸ v.asIdeal) :=
  (Ideal.absNorm_ne_zero_iff v.asIdeal).mp (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))

private theorem resChar_prime (v : HeightOneSpectrum (𝓞 K)) : (resChar K v).Prime := by
  haveI := finite_quot K v
  exact CharP.char_prime_of_ne_zero (𝓞 K ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite (𝓞 K ⧸ v.asIdeal))

private theorem resChar_dvd_absNorm (v : HeightOneSpectrum (𝓞 K)) : resChar K v ∣ Ideal.absNorm v.asIdeal := by
  rw [← natCast_mem_iff]
  exact Ideal.absNorm_mem _

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private theorem ne_resChar_of_not_dvd_absNorm (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : ¬ q ∣ Ideal.absNorm v.asIdeal) :
    q ≠ resChar K v := by
  rintro rfl
  exact hq (resChar_dvd_absNorm K v)

private theorem not_dvd_span_natCast (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : ¬ resChar K v ∣ n) :
    ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, natCast_mem_iff]
  exact hn

private theorem not_dvd_mul_span_natCast (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) {n : ℕ} (hn : ¬ resChar K v ∣ n) :
    ¬ v.asIdeal ∣ 𝔣 * Ideal.span {(n : 𝓞 K)} := by
  intro h
  rcases (Ideal.IsPrime.mul_le v.isPrime).mp (Ideal.le_of_dvd h) with h1 | h2
  · exact hv (Ideal.dvd_iff_le.mpr h1)
  · exact not_dvd_span_natCast K v hn (Ideal.dvd_iff_le.mpr h2)

section Global

variable (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime)

private noncomputable def globalQ : ℕ := (exists_globalPair B₀ hB₀).choose

private noncomputable def globalQ' : ℕ := (exists_globalPair B₀ hB₀).choose_spec.choose

private theorem globalQ_spec : (globalQ B₀ hB₀).Prime ∧ (globalQ' B₀ hB₀).Prime ∧ globalQ B₀ hB₀ ∉ B₀ ∧ globalQ' B₀ hB₀ ∉ B₀ ∧
    globalQ B₀ hB₀ ≠ globalQ' B₀ hB₀ ∧ 8 ∣ globalQ B₀ hB₀ - 1 ∧ 8 ∣ globalQ' B₀ hB₀ - 1 :=
  (exists_globalPair B₀ hB₀).choose_spec.choose_spec

end Global
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section PerCarrier

variable (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) (i : ↥(primeCarriers K 𝔣))

private noncomputable def firstExclusion : Finset ℕ := insert (globalQ B₀ hB₀) (insert (globalQ' B₀ hB₀) B₀)

private theorem exists_firstPrimeOf : ∃ (q : ℕ) (h : (Ideal.absNorm (carrierPlace K 𝔣 i).asIdeal).Coprime q),
    q.Prime ∧ q ∉ firstExclusion B₀ hB₀ ∧ 8 ∣ orderOf (ZMod.unitOfCoprime _ h) :=
  exists_firstPrime_unit (two_le_absNorm K (carrierPlace K 𝔣 i)) (firstExclusion B₀ hB₀)

private noncomputable def firstPrimeOf : ℕ := (exists_firstPrimeOf K 𝔣 B₀ hB₀ i).choose

private theorem absNorm_coprime_firstPrimeOf : (Ideal.absNorm (carrierPlace K 𝔣 i).asIdeal).Coprime (firstPrimeOf K 𝔣 B₀ hB₀ i) :=
  (exists_firstPrimeOf K 𝔣 B₀ hB₀ i).choose_spec.choose

private theorem firstPrimeOf_prime : (firstPrimeOf K 𝔣 B₀ hB₀ i).Prime :=
  (exists_firstPrimeOf K 𝔣 B₀ hB₀ i).choose_spec.choose_spec.1

private theorem firstPrimeOf_notMem_firstExclusion : firstPrimeOf K 𝔣 B₀ hB₀ i ∉ firstExclusion B₀ hB₀ :=
  (exists_firstPrimeOf K 𝔣 B₀ hB₀ i).choose_spec.choose_spec.2.1

private theorem eight_dvd_orderOf_firstUnit :
    8 ∣ orderOf (ZMod.unitOfCoprime _ (absNorm_coprime_firstPrimeOf K 𝔣 B₀ hB₀ i)) :=
  (exists_firstPrimeOf K 𝔣 B₀ hB₀ i).choose_spec.choose_spec.2.2

private theorem firstPrimeOf_notMem : firstPrimeOf K 𝔣 B₀ hB₀ i ∉ B₀ := fun h =>
  firstPrimeOf_notMem_firstExclusion K 𝔣 B₀ hB₀ i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))

private theorem firstPrimeOf_ne_globalQ : firstPrimeOf K 𝔣 B₀ hB₀ i ≠ globalQ B₀ hB₀ := fun h =>
  firstPrimeOf_notMem_firstExclusion K 𝔣 B₀ hB₀ i (h ▸ Finset.mem_insert_self _ _)

private theorem firstPrimeOf_ne_globalQ' : firstPrimeOf K 𝔣 B₀ hB₀ i ≠ globalQ' B₀ hB₀ := fun h =>
  firstPrimeOf_notMem_firstExclusion K 𝔣 B₀ hB₀ i (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

private theorem firstPrimeOf_not_dvd_absNorm : ¬ firstPrimeOf K 𝔣 B₀ hB₀ i ∣ Ideal.absNorm (carrierPlace K 𝔣 i).asIdeal := fun h =>
  (Nat.Prime.one_lt (firstPrimeOf_prime K 𝔣 B₀ hB₀ i)).ne'
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm (absNorm_coprime_firstPrimeOf K 𝔣 B₀ hB₀ i)) h)

private theorem firstPrimeOf_ne_resChar : firstPrimeOf K 𝔣 B₀ hB₀ i ≠ resChar K (carrierPlace K 𝔣 i) :=
  ne_resChar_of_not_dvd_absNorm K _ (firstPrimeOf_not_dvd_absNorm K 𝔣 B₀ hB₀ i)

open Classical in

private noncomputable def secondPrimeOf : ℕ :=
  if globalQ B₀ hB₀ = resChar K (carrierPlace K 𝔣 i) then globalQ' B₀ hB₀ else globalQ B₀ hB₀

private theorem secondPrimeOf_mem : secondPrimeOf K 𝔣 B₀ hB₀ i = globalQ B₀ hB₀ ∨ secondPrimeOf K 𝔣 B₀ hB₀ i = globalQ' B₀ hB₀ := by
  unfold secondPrimeOf; split_ifs <;> simp

private theorem secondPrimeOf_ne_resChar : secondPrimeOf K 𝔣 B₀ hB₀ i ≠ resChar K (carrierPlace K 𝔣 i) := by
  unfold secondPrimeOf
  split_ifs with h
  · exact fun h' => (globalQ_spec B₀ hB₀).2.2.2.2.1 (h.trans h'.symm)
  · exact h

private theorem secondPrimeOf_prime : (secondPrimeOf K 𝔣 B₀ hB₀ i).Prime := by
  rcases secondPrimeOf_mem K 𝔣 B₀ hB₀ i with h | h <;> rw [h]
  · exact (globalQ_spec B₀ hB₀).1
  · exact (globalQ_spec B₀ hB₀).2.1

private theorem secondPrimeOf_notMem : secondPrimeOf K 𝔣 B₀ hB₀ i ∉ B₀ := by
  rcases secondPrimeOf_mem K 𝔣 B₀ hB₀ i with h | h <;> rw [h]
  · exact (globalQ_spec B₀ hB₀).2.2.1
  · exact (globalQ_spec B₀ hB₀).2.2.2.1

private theorem eight_dvd_secondPrimeOf_sub_one : 8 ∣ secondPrimeOf K 𝔣 B₀ hB₀ i - 1 := by
  rcases secondPrimeOf_mem K 𝔣 B₀ hB₀ i with h | h <;> rw [h]
  · exact (globalQ_spec B₀ hB₀).2.2.2.2.2.1
  · exact (globalQ_spec B₀ hB₀).2.2.2.2.2.2

private theorem firstPrimeOf_ne_secondPrimeOf : firstPrimeOf K 𝔣 B₀ hB₀ i ≠ secondPrimeOf K 𝔣 B₀ hB₀ i := by
  rcases secondPrimeOf_mem K 𝔣 B₀ hB₀ i with h | h <;> rw [h]
  · exact firstPrimeOf_ne_globalQ K 𝔣 B₀ hB₀ i
  · exact firstPrimeOf_ne_globalQ' K 𝔣 B₀ hB₀ i

private noncomputable def levelOf : ℕ := firstPrimeOf K 𝔣 B₀ hB₀ i * secondPrimeOf K 𝔣 B₀ hB₀ i

private theorem levelOf_ne_zero : levelOf K 𝔣 B₀ hB₀ i ≠ 0 :=
  mul_ne_zero (firstPrimeOf_prime K 𝔣 B₀ hB₀ i).ne_zero (secondPrimeOf_prime K 𝔣 B₀ hB₀ i).ne_zero

private theorem coprime_firstPrimeOf_secondPrimeOf : (firstPrimeOf K 𝔣 B₀ hB₀ i).Coprime (secondPrimeOf K 𝔣 B₀ hB₀ i) :=
  (Nat.coprime_primes (firstPrimeOf_prime K 𝔣 B₀ hB₀ i) (secondPrimeOf_prime K 𝔣 B₀ hB₀ i)).mpr
    (firstPrimeOf_ne_secondPrimeOf K 𝔣 B₀ hB₀ i)

private theorem not_resChar_dvd_levelOf : ¬ resChar K (carrierPlace K 𝔣 i) ∣ levelOf K 𝔣 B₀ hB₀ i := by
  intro h
  rcases (Nat.Prime.dvd_mul (resChar_prime K _)).mp h with h1 | h2
  · exact firstPrimeOf_ne_resChar K 𝔣 B₀ hB₀ i
      ((Nat.prime_dvd_prime_iff_eq (resChar_prime K _) (firstPrimeOf_prime K 𝔣 B₀ hB₀ i)).mp h1).symm
  · exact secondPrimeOf_ne_resChar K 𝔣 B₀ hB₀ i
      ((Nat.prime_dvd_prime_iff_eq (resChar_prime K _) (secondPrimeOf_prime K 𝔣 B₀ hB₀ i)).mp h2).symm

private theorem carrierPlace_not_dvd_span_levelOf :
    ¬ (carrierPlace K 𝔣 i).asIdeal ∣ Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)} :=
  not_dvd_span_natCast K _ (not_resChar_dvd_levelOf K 𝔣 B₀ hB₀ i)

private theorem carrierPlace_not_dvd_modulus :
    ¬ (carrierPlace K 𝔣 i).asIdeal ∣ 𝔣 * Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)} :=
  not_dvd_mul_span_natCast K 𝔣 _ (carrierPlace_not_dvd K 𝔣 i) (not_resChar_dvd_levelOf K 𝔣 B₀ hB₀ i)

private theorem dvd_modulus : 𝔣 ∣ 𝔣 * Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)} := dvd_mul_right _ _

private theorem modulus_ne_bot (h𝔣 : 𝔣 ≠ ⊥) : 𝔣 * Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)} ≠ ⊥ :=
  mul_ne_zero h𝔣 (fun h => levelOf_ne_zero K 𝔣 B₀ hB₀ i (by
    have h' : Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)} = ⊥ := h
    rwa [Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h'))

private theorem eight_dvd_orderOf_unitGen_secondPrimeOf :
    8 ∣ orderOf (@unitGen (secondPrimeOf K 𝔣 B₀ hB₀ i) ⟨secondPrimeOf_prime K 𝔣 B₀ hB₀ i⟩) :=
  @eight_dvd_orderOf_unitGen _ ⟨secondPrimeOf_prime K 𝔣 B₀ hB₀ i⟩ (eight_dvd_secondPrimeOf_sub_one K 𝔣 B₀ hB₀ i)

end PerCarrier
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {G C₁ C₂ : Type*} [CommGroup G] [CommGroup C₁] [CommGroup C₂]

private def artinAux (σ a : G) (c₁ : C₁) (c₂ g : C₂) : Subgroup (G × (C₁ × C₂)) :=
  Subgroup.closure ({(a, (c₁, c₂)), (σ, (1, g))} : Set (G × (C₁ × C₂)))

variable (σ a : G) (c₁ : C₁) (c₂ g : C₂)

private theorem mem_artinAux_iff (x : G × (C₁ × C₂)) :
    x ∈ artinAux σ a c₁ c₂ g ↔ ∃ i j : ℤ, ((a, (c₁, c₂)) : G × (C₁ × C₂)) ^ i * ((σ, (1, g)) : G × (C₁ × C₂)) ^ j = x := by
  unfold artinAux
  exact Subgroup.mem_closure_pair

private theorem frob_mem_artinAux : ((a, (c₁, c₂)) : G × (C₁ × C₂)) ∈ artinAux σ a c₁ c₂ g :=
  (mem_artinAux_iff σ a c₁ c₂ g _).mpr ⟨1, 0, by rw [zpow_one, zpow_zero, mul_one]⟩

private theorem gen_mem_artinAux : ((σ, (1, g)) : G × (C₁ × C₂)) ∈ artinAux σ a c₁ c₂ g :=
  (mem_artinAux_iff σ a c₁ c₂ g _).mpr ⟨0, 1, by rw [zpow_zero, zpow_one, one_mul]⟩

private theorem artinAux_inf_eq_bot (n : ℕ) (hGn : ∀ x : G, x ^ n = 1) (hc₁ : n ∣ orderOf c₁)
    (hg : ∀ x : C₂, x ∈ Subgroup.zpowers g) (hgn : n ∣ orderOf g) :
    artinAux σ a c₁ c₂ g ⊓ (⊤ : Subgroup G).prod ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hx1⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨i, j, rfl⟩ := (mem_artinAux_iff σ a c₁ c₂ g x).mp hxH
  obtain ⟨-, h2⟩ := Subgroup.mem_prod.mp hx1
  rw [Subgroup.mem_bot] at h2
  obtain ⟨d, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg c₂)

  have hci : c₁ ^ i = 1 := by
    have h := (Prod.ext_iff.mp h2).1
    change c₁ ^ i * (1 : C₁) ^ j = 1 at h
    rwa [one_zpow, mul_one] at h
  have hgdj : g ^ (d * i + j) = 1 := by
    have h := (Prod.ext_iff.mp h2).2
    change (g ^ d) ^ i * g ^ j = 1 at h
    rwa [← zpow_mul, ← zpow_add] at h

  have hni : (n : ℤ) ∣ i := (Int.natCast_dvd_natCast.mpr hc₁).trans (orderOf_dvd_iff_zpow_eq_one.mpr hci)
  have hnj : (n : ℤ) ∣ j := by
    have h : (n : ℤ) ∣ d * i + j := (Int.natCast_dvd_natCast.mpr hgn).trans (orderOf_dvd_iff_zpow_eq_one.mpr hgdj)
    have h' := h.sub (hni.mul_left d)
    rwa [add_sub_cancel_left] at h'

  have hzpow : ∀ (y : G) (k : ℤ), (n : ℤ) ∣ k → y ^ k = 1 := by
    rintro y k ⟨t, rfl⟩
    rw [zpow_mul, zpow_natCast, hGn, one_zpow]
  rw [Subgroup.mem_bot]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change a ^ i * σ ^ j = 1
    rw [hzpow a i hni, hzpow σ j hnj, one_mul]
  · change c₁ ^ i * (1 : C₁) ^ j = 1
    rw [hci, one_zpow, one_mul]
  · change (g ^ d) ^ i * g ^ j = 1
    rwa [← zpow_mul, ← zpow_add]

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField
open scoped IsMulCommutative

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
variable {C₁ C₂ : Type*} [CommGroup C₁] [CommGroup C₂] (ψ : (ZMod m)ˣ ≃* C₁ × C₂)
variable (σ a : L ≃ₐ[K] L) (c₁ : C₁) (c₂ g : C₂)

private noncomputable def auxFieldArtin : IntermediateField K M :=
  auxField L hζ ψ (artinAux σ a c₁ c₂ g)

variable [FiniteDimensional K M]

private theorem mem_fixingSubgroup_auxFieldArtin_of_galProd_eq {τ : M ≃ₐ[K] M} (hτ : galProd L hζ ψ τ = (a, (c₁, c₂))) :
    τ ∈ (auxFieldArtin L hζ ψ σ a c₁ c₂ g).fixingSubgroup :=
  mem_fixingSubgroup_auxField L hζ ψ (hτ ▸ frob_mem_artinAux σ a c₁ c₂ g)

private theorem mem_fixingSubgroup_auxFieldArtin_of_galProd_eq_gen {γ : M ≃ₐ[K] M} (hγ : galProd L hζ ψ γ = (σ, (1, g))) :
    γ ∈ (auxFieldArtin L hζ ψ σ a c₁ c₂ g).fixingSubgroup :=
  mem_fixingSubgroup_auxField L hζ ψ (hγ ▸ gen_mem_artinAux σ a c₁ c₂ g)

variable [IsGalois K M]

private theorem adjoin_auxFieldArtin_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) (n : ℕ) (hGn : ∀ x : L ≃ₐ[K] L, x ^ n = 1) (hc₁ : n ∣ orderOf c₁)
    (hg : ∀ x : C₂, x ∈ Subgroup.zpowers g) (hgn : n ∣ orderOf g) :
    IntermediateField.adjoin (auxFieldArtin L hζ ψ σ a c₁ c₂ g) ({ζ} : Set M) = ⊤ :=
  adjoin_auxField_eq_top L hζ ψ htop (artinAux_inf_eq_bot σ a c₁ c₂ g n hGn hc₁ hg hgn)

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped IsMulCommutative

section Frob

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (L : IntermediateField K M) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
variable {C₁ C₂ : Type*} [CommGroup C₁] [CommGroup C₂] (ψ : (ZMod m)ˣ ≃* C₁ × C₂)
variable (σ : L ≃ₐ[K] L) (g : C₂) (v : HeightOneSpectrum (𝓞 K))

private def frobA : L ≃ₐ[K] L := (galProd L hζ ψ (artinFrob K M v)).1

private def frobC : C₁ × C₂ := (galProd L hζ ψ (artinFrob K M v)).2

omit [IsMulCommutative (L ≃ₐ[K] L)] in
private theorem galProd_artinFrob_eq : galProd L hζ ψ (artinFrob K M v) = (frobA K M L hζ ψ v, ((frobC K M L hζ ψ v).1, (frobC K M L hζ ψ v).2)) :=
  Prod.ext rfl (Prod.ext rfl rfl)

private def datumField : IntermediateField K M :=
  auxFieldArtin L hζ ψ σ (frobA K M L hζ ψ v) (frobC K M L hζ ψ v).1 (frobC K M L hζ ψ v).2 g

private theorem artinFrob_mem_fixingSubgroup_datumField : artinFrob K M v ∈ (datumField K M L hζ ψ σ g v).fixingSubgroup :=
  mem_fixingSubgroup_auxFieldArtin_of_galProd_eq L hζ ψ σ _ _ _ g (galProd_artinFrob_eq K M L hζ ψ v)

private def datumPrime : HeightOneSpectrum (𝓞 ↥(datumField K M L hζ ψ σ g v)) where
  asIdeal := (primeAbove K M v).under (𝓞 ↥(datumField K M L hζ ψ σ g v))
  isPrime := Ideal.IsPrime.under _ _
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField (Ideal.IsMaximal.under _ _) (RingOfIntegers.not_isField _)

private theorem datumPrime_asIdeal : (datumPrime K M L hζ ψ σ g v).asIdeal = (primeAbove K M v).under (𝓞 ↥(datumField K M L hζ ψ σ g v)) :=
  rfl

private theorem datumPrime_under : (datumPrime K M L hζ ψ σ g v).asIdeal.under (𝓞 K) = v.asIdeal := by
  rw [datumPrime_asIdeal, Ideal.under_under, under_primeAbove]

private theorem inertiaDeg_datumPrime : v.asIdeal.inertiaDeg' (datumPrime K M L hζ ψ σ g v).asIdeal = 1 := by
  have h := inertiaDeg_under_eq_one_of_fix (artinFrob_mem_fixingSubgroup_datumField K M L hζ ψ σ g v) (primeAbove K M v)
    (isArithFrobAt_artinFrob K M v)
  rwa [under_primeAbove] at h

private theorem datumPrime_not_dvd {𝔪 : Ideal (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪) :
    ¬ (datumPrime K M L hζ ψ σ g v).asIdeal ∣ modulusExt K ↥(datumField K M L hζ ψ σ g v) 𝔪 :=
  not_dvd_modulusExt_of_under K 𝔪 hv (datumPrime_under K M L hζ ψ σ g v)

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem frobC_eq (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) : frobC K M L hζ ψ v = ψ (M4aP2.normClass K m v) :=
  galProd_artinFrob_snd K M L hζ ψ v hm

omit [NumberField K] [NumberField M] [IsGalois K M] in

private theorem isMulCommutative_gal_of_galProd_injective (h : Function.Injective (galProd L hζ ψ)) : IsMulCommutative (M ≃ₐ[K] M) :=
  ⟨⟨fun a b => h (by rw [map_mul, map_mul, mul_comm])⟩⟩

omit [NumberField K] [NumberField M] [IsGalois K M] in
include hζ ψ in

private theorem isMulCommutative_gal_of_sup_adjoin_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) : IsMulCommutative (M ≃ₐ[K] M) :=
  isMulCommutative_gal_of_galProd_injective K M L hζ ψ (galProd_injective L hζ ψ htop)

private theorem isMulCommutative_gal_datumField [IsMulCommutative (M ≃ₐ[K] M)] :
    IsMulCommutative (M ≃ₐ[↥(datumField K M L hζ ψ σ g v)] M) :=
  isMulCommutative_gal_intermediateField (datumField K M L hζ ψ σ g v)

end Frob
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

section CRT

variable {a b : ℕ}

private def crtUnits (h : a.Coprime b) : (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

private theorem val_crtUnits_fst (h : a.Coprime b) [NeZero (a * b)] (u : (ZMod (a * b))ˣ) :
    ((crtUnits h u).1 : ZMod a) = (((u : ZMod (a * b)).val : ℕ) : ZMod a) := by
  rw [show ((crtUnits h u).1 : ZMod a) = (ZMod.cast (u : ZMod (a * b)) : ZMod a × ZMod b).1 from rfl, ZMod.cast_eq_val,
    Prod.fst_natCast]

private theorem crtUnits_fst_unitOfCoprime (h : a.Coprime b) [NeZero (a * b)] {N : ℕ} (hN : N.Coprime (a * b)) (hNa : N.Coprime a) :
    (crtUnits h (ZMod.unitOfCoprime N hN)).1 = ZMod.unitOfCoprime N hNa := by
  refine Units.ext ?_
  rw [val_crtUnits_fst, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff',
    Nat.mod_mod_of_dvd N (dvd_mul_right a b)]

end CRT
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section PerI

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
variable (𝔣 : Ideal (𝓞 K)) (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) (σ : L ≃ₐ[K] L) (i : ↥(primeCarriers K 𝔣))

private scoped instance neZero_levelOf : NeZero (levelOf K 𝔣 B₀ hB₀ i) := ⟨levelOf_ne_zero K 𝔣 B₀ hB₀ i⟩

private scoped instance fact_secondPrimeOf_prime : Fact (secondPrimeOf K 𝔣 B₀ hB₀ i).Prime := ⟨secondPrimeOf_prime K 𝔣 B₀ hB₀ i⟩

private abbrev Amb : Type _ := ↥(CycM K L (levelOf K 𝔣 B₀ hB₀ i))

private def ψlevel : (ZMod (levelOf K 𝔣 B₀ hB₀ i))ˣ ≃* (ZMod (firstPrimeOf K 𝔣 B₀ hB₀ i))ˣ × (ZMod (secondPrimeOf K 𝔣 B₀ hB₀ i))ˣ :=
  crtUnits (coprime_firstPrimeOf_secondPrimeOf K 𝔣 B₀ hB₀ i)

private def σlevel : (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) ≃ₐ[K] (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) :=
  (galEquivL'M K L (levelOf K 𝔣 B₀ hB₀ i)).symm σ

private scoped instance isMulCommutative_galL'M (m : ℕ) [NeZero m] : IsMulCommutative ((L'M K L m) ≃ₐ[K] (L'M K L m)) :=
  ⟨⟨fun x y => (galEquivL'M K L m).injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

private def Efield : IntermediateField K (Amb K L 𝔣 B₀ hB₀ i) :=
  datumField K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i))
    (ψlevel K 𝔣 B₀ hB₀ i) (σlevel K L 𝔣 B₀ hB₀ σ i) (unitGen (secondPrimeOf K 𝔣 B₀ hB₀ i)) (carrierPlace K 𝔣 i)

private abbrev Nfield : IntermediateField K (Amb K L 𝔣 B₀ hB₀ i) := L'M K L (levelOf K 𝔣 B₀ hB₀ i) ⊔ Efield K L 𝔣 B₀ hB₀ σ i

private abbrev modulus : Ideal (𝓞 K) := 𝔣 * Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)}

private scoped instance numberField_Efield : NumberField (Efield K L 𝔣 B₀ hB₀ σ i) := instNFE K L _ _

private scoped instance numberField_Nfield : NumberField (Nfield K L 𝔣 B₀ hB₀ σ i) := instNFsup K L _ _

private scoped instance isMulCommutative_galAmb : IsMulCommutative ((Amb K L 𝔣 B₀ hB₀ i) ≃ₐ[K] (Amb K L 𝔣 B₀ hB₀ i)) :=
  isMulCommutative_gal_of_sup_adjoin_eq_top K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i))
    (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i)) (ψlevel K 𝔣 B₀ hB₀ i) (L'M_sup_adjoin_eq_top K L (levelOf K 𝔣 B₀ hB₀ i))

private theorem isGalois_of_abelian (F : IntermediateField K (Amb K L 𝔣 B₀ hB₀ i)) : IsGalois K F :=
  IsGalois.of_algEquiv (IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup F))

private scoped instance isGalois_Nfield : IsGalois K (Nfield K L 𝔣 B₀ hB₀ σ i) := isGalois_of_abelian K L 𝔣 B₀ hB₀ i _

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance isGalois_EN : IsGalois (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i) :=
  IsGalois.tower_top_of_isGalois K (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i)

set_option synthInstance.maxHeartbeats 1600000 in
private scoped instance isScalarTower_ENM : IsScalarTower (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i) (Amb K L 𝔣 B₀ hB₀ i) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)

set_option synthInstance.maxHeartbeats 1600000 in

private scoped instance isMulCommutative_galEN : IsMulCommutative ((Nfield K L 𝔣 B₀ hB₀ σ i) ≃ₐ[Efield K L 𝔣 B₀ hB₀ σ i] (Nfield K L 𝔣 B₀ hB₀ σ i)) :=
  ⟨⟨fun x y => resHom_injective_sup_L K L (levelOf K 𝔣 B₀ hB₀ i) (Efield K L 𝔣 B₀ hB₀ σ i) (by rw [map_mul, map_mul, mul_comm])⟩⟩

private scoped instance isMulCommutative_galEM : IsMulCommutative ((Amb K L 𝔣 B₀ hB₀ i) ≃ₐ[Efield K L 𝔣 B₀ hB₀ σ i] (Amb K L 𝔣 B₀ hB₀ i)) :=
  isMulCommutative_gal_datumField K _ _ _ _ _ _ _

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem frobC_fst_eq :
    (frobC K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i))
      (ψlevel K 𝔣 B₀ hB₀ i) (carrierPlace K 𝔣 i)).1
      = ZMod.unitOfCoprime _ (absNorm_coprime_firstPrimeOf K 𝔣 B₀ hB₀ i) := by
  have hm := carrierPlace_not_dvd_span_levelOf K 𝔣 B₀ hB₀ i
  have hcop := M4aP2.absNorm_coprime_of_not_dvd K (levelOf K 𝔣 B₀ hB₀ i) (carrierPlace K 𝔣 i) hm
  rw [frobC_eq K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) _ _ _ hm, M4aP2.normClass, dif_pos hcop]
  haveI : NeZero (firstPrimeOf K 𝔣 B₀ hB₀ i * secondPrimeOf K 𝔣 B₀ hB₀ i) := neZero_levelOf K 𝔣 B₀ hB₀ i
  exact crtUnits_fst_unitOfCoprime (coprime_firstPrimeOf_secondPrimeOf K 𝔣 B₀ hB₀ i) hcop _

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem eight_dvd_orderOf_frobC_fst :
    8 ∣ orderOf (frobC K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i))
      (ψlevel K 𝔣 B₀ hB₀ i) (carrierPlace K 𝔣 i)).1 := by
  rw [frobC_fst_eq]
  exact eight_dvd_orderOf_firstUnit K 𝔣 B₀ hB₀ i

omit [NumberField K] [IsGalois K L] in

private theorem pow_eight_galL'M (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) (m : ℕ) [NeZero m] (x : (L'M K L m) ≃ₐ[K] (L'M K L m)) : x ^ 8 = 1 :=
  (galEquivL'M K L m).injective (by rw [map_pow, map_one, hexp])

private theorem adjoin_Efield_eq_top (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) :
    (IntermediateField.adjoin (Efield K L 𝔣 B₀ hB₀ σ i) ({ζM K L (levelOf K 𝔣 B₀ hB₀ i)} : Set (Amb K L 𝔣 B₀ hB₀ i))) = ⊤ :=
  adjoin_auxFieldArtin_eq_top (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i)) (ψlevel K 𝔣 B₀ hB₀ i)
    (σlevel K L 𝔣 B₀ hB₀ σ i) _ _ _ _ (L'M_sup_adjoin_eq_top K L (levelOf K 𝔣 B₀ hB₀ i)) 8
    (pow_eight_galL'M K L hexp _) (eight_dvd_orderOf_frobC_fst K L 𝔣 B₀ hB₀ i)
    (unitGen_generates (secondPrimeOf K 𝔣 B₀ hB₀ i)) (eight_dvd_orderOf_unitGen_secondPrimeOf K 𝔣 B₀ hB₀ i)

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem span_level_dvd_modulusExt (E : Type*) [Field E] [NumberField E] [Algebra K E] :
    Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 E)} ∣ modulusExt K E (modulus K 𝔣 B₀ hB₀ i) :=
  ⟨modulusExt K E 𝔣, by
    rw [modulusExt, modulusExt, Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_natCast, mul_comm]⟩

omit [IsMulCommutative (L ≃ₐ[K] L)] in
omit [NumberField L] [IsGalois K L] in
private theorem ne_bot_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h𝔣 : IsAdmissibleModulus K L 𝔣) : 𝔣 ≠ ⊥ := h𝔣.1

set_option synthInstance.maxHeartbeats 1600000 in

private def artinFieldCore_of (h𝔣 : IsAdmissibleModulus K L 𝔣) (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) : ArtinFieldCore K L 𝔣 i where
  E := Efield K L 𝔣 B₀ hB₀ σ i
  N := Nfield K L 𝔣 B₀ hB₀ σ i
  Θ := Amb K L 𝔣 B₀ hB₀ i
  instNFE := numberField_Efield K L 𝔣 B₀ hB₀ σ i
  instNFN := numberField_Nfield K L 𝔣 B₀ hB₀ σ i
  instAEN := instAlgEN K L _ _
  instALN := instAlgLN K L _ _
  instSTKEN := instSTKEN K L _ _
  instSTKLN := instSTKLN K L _ _
  instSTENΘ := isScalarTower_ENM K L 𝔣 B₀ hB₀ σ i
  instGEN := isGalois_EN K L 𝔣 B₀ hB₀ σ i
  instCN := isMulCommutative_galEN K L 𝔣 B₀ hB₀ σ i
  instCΘ := isMulCommutative_galEM K L 𝔣 B₀ hB₀ σ i
  𝔪 := modulus K 𝔣 B₀ hB₀ i
  h𝔪 := dvd_modulus K 𝔣 B₀ hB₀ i
  v := carrierPlace K 𝔣 i
  hv𝔪 := carrierPlace_not_dvd_modulus K 𝔣 B₀ hB₀ i
  hvi := primeCarrier_carrierPlace K 𝔣 i
  w := datumPrime K (Amb K L 𝔣 B₀ hB₀ i) (L'M K L (levelOf K 𝔣 B₀ hB₀ i)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i))
    (ψlevel K 𝔣 B₀ hB₀ i) (σlevel K L 𝔣 B₀ hB₀ σ i) (unitGen (secondPrimeOf K 𝔣 B₀ hB₀ i)) (carrierPlace K 𝔣 i)
  hw := datumPrime_not_dvd K _ _ _ _ _ _ _ (carrierPlace_not_dvd_modulus K 𝔣 B₀ hB₀ i)
  hwv := datumPrime_under K _ _ _ _ _ _ _
  hf := inertiaDeg_datumPrime K _ _ _ _ _ _ _
  q := levelOf K 𝔣 B₀ hB₀ i
  ζ := ζM K L (levelOf K 𝔣 B₀ hB₀ i)
  hζ := isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ i)
  htop := adjoin_Efield_eq_top K L 𝔣 B₀ hB₀ σ i hexp
  hq𝔪 := @span_level_dvd_modulusExt K _ _ 𝔣 B₀ hB₀ i (Efield K L 𝔣 B₀ hB₀ σ i) _ (numberField_Efield K L 𝔣 B₀ hB₀ σ i) _
  hunr := hunr_of_isAdmissibleModulus K L (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i) (Amb K L 𝔣 B₀ hB₀ i) h𝔣
    (dvd_modulus K 𝔣 B₀ hB₀ i) (resHom_injective_sup_L K L (levelOf K 𝔣 B₀ hB₀ i) (Efield K L 𝔣 B₀ hB₀ σ i))
  hadm := isAdmissibleModulus_ext K L (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i) h𝔣 (dvd_modulus K 𝔣 B₀ hB₀ i)
    (modulus_ne_bot K 𝔣 B₀ hB₀ i (ne_bot_of_isAdmissibleModulus K L h𝔣))
    (resHom_injective_sup_L K L (levelOf K 𝔣 B₀ hB₀ i) (Efield K L 𝔣 B₀ hB₀ σ i))
  hI_E := hI_E_of_isAdmissibleModulus K L (Efield K L 𝔣 B₀ hB₀ σ i) (Nfield K L 𝔣 B₀ hB₀ σ i) h𝔣 (dvd_modulus K 𝔣 B₀ hB₀ i)
  hresInj := resHom_injective_sup_L K L (levelOf K 𝔣 B₀ hB₀ i) (Efield K L 𝔣 B₀ hB₀ σ i)

private def artinFieldCoreFamily (h𝔣 : IsAdmissibleModulus K L 𝔣) (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) :
    ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore K L 𝔣 i :=
  fun i => artinFieldCore_of K L 𝔣 B₀ hB₀ σ i h𝔣 hexp

end PerI
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

section Levels

variable {m M : ℕ} [NeZero m] [NeZero M]

omit [NumberField K] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
private theorem ζΩ_mem_adjoin_of_dvd (h : m ∣ M) : ζΩ L m ∈ IntermediateField.adjoin K {ζΩ L M} := by
  obtain ⟨k, hk⟩ := h
  have hξ : IsPrimitiveRoot (ζΩ L M ^ k) m := (isPrimitiveRoot_ζΩ L M).pow (NeZero.pos M) (by rw [hk, mul_comm])
  obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (isPrimitiveRoot_ζΩ L m).pow_eq_one
  rw [← hi, ← pow_mul]
  exact pow_mem (mem_adjoin_simple_self K _) _

omit [NumberField K] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem CycM_mono (h : m ∣ M) : CycM K L m ≤ CycM K L M :=
  sup_le_sup_left (adjoin_simple_le_iff.mpr (ζΩ_mem_adjoin_of_dvd K L h)) _

private def inclM (h : m ∣ M) : ↥(CycM K L m) →ₐ[K] ↥(CycM K L M) := IntermediateField.inclusion (CycM_mono K L h)

omit [NumberField K] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
@[scoped simp] private theorem coe_inclM (h : m ∣ M) (x : ↥(CycM K L m)) : ((inclM K L h x : ↥(CycM K L M)) : Ω L) = x :=
  IntermediateField.coe_inclusion (CycM_mono K L h) x

omit [NumberField K] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
private theorem inclM_injective (h : m ∣ M) : Function.Injective (inclM K L h) := (inclM K L h).toRingHom.injective

end Levels
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section GalM

variable (M : ℕ) [NeZero M]

private scoped instance isMulCommutative_galCycM : IsMulCommutative (↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) :=
  ⟨⟨fun a b => galProd_injective (L'M K L M) (isPrimitiveRoot_ζM K L M) (MulEquiv.refl ((ZMod M)ˣ))
    (L'M_sup_adjoin_eq_top K L M) (by rw [map_mul, map_mul, mul_comm])⟩⟩

private theorem isGalois_of_le_CycM (F : IntermediateField K ↥(CycM K L M)) : IsGalois K F :=
  IsGalois.of_algEquiv (IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup F))

end GalM
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Pair

set_option synthInstance.maxHeartbeats 1600000

variable {mi mj M : ℕ} [NeZero mi] [NeZero mj] [NeZero M] (hi : mi ∣ M) (hj : mj ∣ M)
  (Ei : IntermediateField K ↥(CycM K L mi)) (Ej : IntermediateField K ↥(CycM K L mj))

private def pairField : IntermediateField K ↥(CycM K L M) := Ei.map (inclM K L hi) ⊔ Ej.map (inclM K L hj)

private abbrev pairN : IntermediateField K ↥(CycM K L M) := L'M K L M ⊔ pairField K L hi hj Ei Ej

private scoped instance numberField_pairField : NumberField ↥(pairField K L hi hj Ei Ej) := instNFE K L _ _

private scoped instance numberField_pairN : NumberField ↥(pairN K L hi hj Ei Ej) := instNFsup K L _ _

private def toPairFieldI : ↥Ei →ₐ[K] ↥(pairField K L hi hj Ei Ej) :=
  (IntermediateField.inclusion (le_sup_left (b := Ej.map (inclM K L hj)))).comp (Ei.equivMap (inclM K L hi)).toAlgHom

private def toPairFieldJ : ↥Ej →ₐ[K] ↥(pairField K L hi hj Ei Ej) :=
  (IntermediateField.inclusion (le_sup_right (a := Ei.map (inclM K L hi)))).comp (Ej.equivMap (inclM K L hj)).toAlgHom

private scoped instance algPairI : Algebra ↥Ei ↥(pairField K L hi hj Ei Ej) := (toPairFieldI K L hi hj Ei Ej).toRingHom.toAlgebra

private scoped instance algPairJ : Algebra ↥Ej ↥(pairField K L hi hj Ei Ej) := (toPairFieldJ K L hi hj Ei Ej).toRingHom.toAlgebra

private scoped instance isScalarTower_pairI : IsScalarTower K ↥Ei ↥(pairField K L hi hj Ei Ej) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => ((toPairFieldI K L hi hj Ei Ej).commutes x).symm)

private scoped instance isScalarTower_pairJ : IsScalarTower K ↥Ej ↥(pairField K L hi hj Ei Ej) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => ((toPairFieldJ K L hi hj Ei Ej).commutes x).symm)

private scoped instance isGalois_pairN : IsGalois K ↥(pairN K L hi hj Ei Ej) := isGalois_of_le_CycM K L M _

private scoped instance isGalois_pairEN : IsGalois ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) :=
  IsGalois.tower_top_of_isGalois K ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej)

private scoped instance isMulCommutative_galPairEN :
    IsMulCommutative (↥(pairN K L hi hj Ei Ej) ≃ₐ[↥(pairField K L hi hj Ei Ej)] ↥(pairN K L hi hj Ei Ej)) :=
  ⟨⟨fun x y => resHom_injective_sup_L K L M (pairField K L hi hj Ei Ej) (by rw [map_mul, map_mul, mul_comm])⟩⟩

variable {𝔣 𝔪'' : Ideal (𝓞 K)}

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem hI_pair (h𝔣 : IsAdmissibleModulus K L 𝔣) (h'' : 𝔣 ∣ 𝔪'') (w' : HeightOneSpectrum (𝓞 ↥(pairField K L hi hj Ei Ej)))
    (hw' : ¬ w'.asIdeal ∣ modulusExt K ↥(pairField K L hi hj Ei Ej) 𝔪'') :
    ((primeAbove ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) w').under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥ :=
  hI_E_of_isAdmissibleModulus K L ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) h𝔣 h'' w' hw'

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem hadm_pair (h𝔣 : IsAdmissibleModulus K L 𝔣) (h'' : 𝔣 ∣ 𝔪'') (h0 : 𝔪'' ≠ ⊥) :
    IsAdmissibleModulus ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) (modulusExt K ↥(pairField K L hi hj Ei Ej) 𝔪'') :=
  isAdmissibleModulus_ext K L ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) h𝔣 h'' h0
    (resHom_injective_sup_L K L M (pairField K L hi hj Ei Ej))

private theorem hcompat_pair (h𝔣 : IsAdmissibleModulus K L 𝔣) (h'' : 𝔣 ∣ 𝔪'') (B : ↥(coprimeToModulus ↥(pairField K L hi hj Ei Ej) (modulusExt K ↥(pairField K L hi hj Ei Ej) 𝔪''))) :
    artinSymbol K L 𝔣 (ctmInclusion K h'' (relNormCTM K ↥(pairField K L hi hj Ei Ej) 𝔪'' B))
      = resHom K L ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej)
          (artinSymbol ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) (modulusExt K ↥(pairField K L hi hj Ei Ej) 𝔪'') B) := by
  rw [artinSymbol_ctmInclusion K L h'']
  exact DFunLike.congr_fun (artinSymbol_comp_relNormCTM_eq K L ↥(pairField K L hi hj Ei Ej) ↥(pairN K L hi hj Ei Ej) 𝔪''
    (hI_pair K L hi hj Ei Ej h𝔣 h'')) B

end Pair
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

private theorem exists_ζΩ_eq_pow {m M : ℕ} [NeZero m] [NeZero M] (h : m ∣ M) : ∃ e : ℕ, ζΩ L m = ζΩ L M ^ e := by
  obtain ⟨k, hk⟩ := h
  have hξ : IsPrimitiveRoot (ζΩ L M ^ k) m := (isPrimitiveRoot_ζΩ L M).pow (NeZero.pos M) (by rw [hk, mul_comm])
  obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (isPrimitiveRoot_ζΩ L m).pow_eq_one
  exact ⟨k * i, by rw [pow_mul, hi]⟩

section Coe

variable (m : ℕ) [NeZero m]

omit [NumberField K] [NumberField L] [IsGalois K L] in
private theorem coe_toL' (a : L) : ((toL' K L a : ↥(L' K L)) : Ω L) = algebraMap L (Ω L) a :=
  AlgEquiv.ofInjective_apply (IsScalarTower.toAlgHom K L (Ω L)) (IsScalarTower.toAlgHom K L (Ω L)).toRingHom.injective a

omit [NumberField K] [IsGalois K L] in
private theorem coe_toL'M (a : L) : (((toL'M K L m a : ↥(L'M K L m)) : ↥(CycM K L m)) : Ω L) = algebraMap L (Ω L) a := by
  have h1 : ((IntermediateField.restrict_algEquiv (show L' K L ≤ CycM K L m from le_sup_left) (toL' K L a) :
      ↥(IntermediateField.restrict (show L' K L ≤ CycM K L m from le_sup_left))) : ↥(CycM K L m))
        = IntermediateField.inclusion (show L' K L ≤ CycM K L m from le_sup_left) (toL' K L a) :=
    AlgEquiv.ofInjective_apply _ (IntermediateField.inclusion (show L' K L ≤ CycM K L m from le_sup_left)).toRingHom.injective _
  rw [toL'M, AlgEquiv.trans_apply]
  refine (congrArg (fun y : ↥(CycM K L m) => (y : Ω L)) h1).trans ?_
  rw [IntermediateField.coe_inclusion, coe_toL']

end Coe
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section LevelRes

variable (m : ℕ) {M : ℕ} [NeZero m] [NeZero M] [hmM : Fact (m ∣ M)]

private scoped instance algLevel : Algebra ↥(CycM K L m) ↥(CycM K L M) := (inclM K L hmM.out).toRingHom.toAlgebra

private scoped instance isScalarTower_level : IsScalarTower K ↥(CycM K L m) ↥(CycM K L M) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => ((inclM K L hmM.out).commutes x).symm)

private def resLevel : (↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) →* (↥(CycM K L m) ≃ₐ[K] ↥(CycM K L m)) :=
  AlgEquiv.restrictNormalHom ↥(CycM K L m)

private theorem inclM_resLevel (γ : ↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) (x : ↥(CycM K L m)) :
    inclM K L hmM.out (resLevel K L m γ x) = γ (inclM K L hmM.out x) :=
  AlgEquiv.restrictNormal_commutes γ ↥(CycM K L m) x

omit [NumberField K] [IsGalois K L] in
private theorem exists_inclM_ζM_eq_pow : ∃ e : ℕ, inclM K L hmM.out (ζM K L m) = ζM K L M ^ e := by
  obtain ⟨e, he⟩ := exists_ζΩ_eq_pow L hmM.out
  exact ⟨e, Subtype.ext (by rw [coe_inclM, val_ζM, SubmonoidClass.coe_pow, val_ζM, he])⟩

private theorem resLevel_ζM (γ : ↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) {u : ℕ} (hγ : γ (ζM K L M) = ζM K L M ^ u) :
    resLevel K L m γ (ζM K L m) = ζM K L m ^ u := by
  apply inclM_injective K L hmM.out
  obtain ⟨e, he⟩ := exists_inclM_ζM_eq_pow K L m (M := M)
  rw [inclM_resLevel, he, map_pow, hγ, map_pow, he, ← pow_mul, ← pow_mul, mul_comm]

private theorem autToPow_resLevel (γ : ↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) :
    (isPrimitiveRoot_ζM K L m).autToPow K (resLevel K L m γ)
      = ZMod.unitsMap hmM.out ((isPrimitiveRoot_ζM K L M).autToPow K γ) := by
  set u := (isPrimitiveRoot_ζM K L M).autToPow K γ with hu
  have hM : γ (ζM K L M) = ζM K L M ^ (u : ZMod M).val := ((isPrimitiveRoot_ζM K L M).autToPow_spec K γ).symm
  have hres : resLevel K L m γ (ζM K L m) = ζM K L m ^ (u : ZMod M).val := resLevel_ζM K L m γ hM
  have hspec := (isPrimitiveRoot_ζM K L m).autToPow_spec K (resLevel K L m γ)
  rw [hres] at hspec
  have hmod := ((isPrimitiveRoot_ζM K L m).isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq.mp hspec
  rw [← (isPrimitiveRoot_ζM K L m).eq_orderOf, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
  apply Units.ext
  rw [hmod, ZMod.unitsMap_def]
  show _ = ZMod.castHom hmM.out (ZMod m) (u : ZMod M)
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

omit [NumberField K] [IsGalois K L] in

private theorem inclM_toL'M (a : L) : inclM K L hmM.out (toL'M K L m a : ↥(CycM K L m)) = (toL'M K L M a : ↥(CycM K L M)) :=
  Subtype.ext (by rw [coe_inclM, coe_toL'M, coe_toL'M])

omit [NumberField K] in

private theorem algebraMap_galEquivL'M_restrict (n : ℕ) [NeZero n] (φ : ↥(CycM K L n) ≃ₐ[K] ↥(CycM K L n)) (a : L) :
    algebraMap L (Ω L) (galEquivL'M K L n (AlgEquiv.restrictNormalHom (L'M K L n) φ) a)
      = ((φ (toL'M K L n a : ↥(CycM K L n)) : ↥(CycM K L n)) : Ω L) := by
  show algebraMap L (Ω L) ((toL'M K L n).symm (AlgEquiv.restrictNormalHom (L'M K L n) φ (toL'M K L n a))) = _
  rw [← coe_toL'M K L n, AlgEquiv.apply_symm_apply, AlgEquiv.restrictNormalHom_apply]

private theorem galEquivL'M_restrict_resLevel (γ : ↥(CycM K L M) ≃ₐ[K] ↥(CycM K L M)) :
    galEquivL'M K L m (AlgEquiv.restrictNormalHom (L'M K L m) (resLevel K L m γ))
      = galEquivL'M K L M (AlgEquiv.restrictNormalHom (L'M K L M) γ) := by
  apply AlgEquiv.ext
  intro a
  apply (algebraMap L (Ω L)).injective
  rw [algebraMap_galEquivL'M_restrict, algebraMap_galEquivL'M_restrict, ← coe_inclM K L hmM.out, inclM_resLevel,
    inclM_toL'M]

end LevelRes
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

section UnitByPrime

variable (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)

private def primeProd : ℕ := ∏ p ∈ S, p

include hS in
private theorem primeProd_ne_zero : primeProd S ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero

private theorem dvd_primeProd {p : ℕ} (hp : p ∈ S) : p ∣ primeProd S := Finset.dvd_prod_of_mem _ hp

include hS in
private theorem primeFactors_primeProd : (primeProd S).primeFactors = S := Nat.primeFactors_prod hS

include hS in
private theorem pairwise_coprime_coe : Pairwise (Function.onFun Nat.Coprime fun p : S => (p : ℕ)) := fun p q hne =>
  (Nat.coprime_primes (hS _ p.2) (hS _ q.2)).mpr fun h => hne (Subtype.ext h)

private def crtS : ZMod (primeProd S) ≃+* (Π p : S, ZMod p) :=
  (ZMod.ringEquivCongr (Finset.prod_coe_sort S (fun p => p)).symm).trans
    (ZMod.prodEquivPi (fun p : S => (p : ℕ)) (pairwise_coprime_coe S hS))

private theorem crtS_apply (x : ZMod (primeProd S)) (p : S) : crtS S hS x p = ZMod.castHom (dvd_primeProd S p.2) (ZMod p) x :=
  RingHom.congr_fun (RingHom.ext_zmod ((Pi.evalRingHom (fun q : S => ZMod q) p).comp (crtS S hS).toRingHom)
    (ZMod.castHom (dvd_primeProd S p.2) (ZMod p))) x

private def unitOfTargets (t : (p : ℕ) → (ZMod p)ˣ) : (ZMod (primeProd S))ˣ where
  val := (crtS S hS).symm fun p => (t p : ZMod p)
  inv := (crtS S hS).symm fun p => ((t p)⁻¹ : (ZMod p)ˣ)
  val_inv := by
    rw [← map_mul, ← map_one (crtS S hS).symm]
    exact congrArg _ (funext fun p => (t p).mul_inv)
  inv_val := by
    rw [← map_mul, ← map_one (crtS S hS).symm]
    exact congrArg _ (funext fun p => (t p).inv_mul)

private theorem unitsMap_unitOfTargets (t : (p : ℕ) → (ZMod p)ˣ) {p : ℕ} (hp : p ∈ S) :
    ZMod.unitsMap (dvd_primeProd S hp) (unitOfTargets S hS t) = t p := by
  apply Units.ext
  show ZMod.castHom (dvd_primeProd S hp) (ZMod p) ((crtS S hS).symm fun q : S => (t q : ZMod q)) = (t p : ZMod p)
  rw [← crtS_apply S hS _ ⟨p, hp⟩, RingEquiv.apply_symm_apply]

end UnitByPrime
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section PairLevel

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime)
  (i j : ↥(primeCarriers K 𝔣))

private def pairPrimes : Finset ℕ :=
  {firstPrimeOf K 𝔣 B₀ hB₀ i, secondPrimeOf K 𝔣 B₀ hB₀ i, firstPrimeOf K 𝔣 B₀ hB₀ j, secondPrimeOf K 𝔣 B₀ hB₀ j}

private theorem mem_pairPrimes_iff (p : ℕ) : p ∈ pairPrimes K 𝔣 B₀ hB₀ i j ↔
    p = firstPrimeOf K 𝔣 B₀ hB₀ i ∨ p = secondPrimeOf K 𝔣 B₀ hB₀ i ∨ p = firstPrimeOf K 𝔣 B₀ hB₀ j ∨ p = secondPrimeOf K 𝔣 B₀ hB₀ j := by
  simp only [pairPrimes, Finset.mem_insert, Finset.mem_singleton]

private theorem pairPrimes_prime : ∀ p ∈ pairPrimes K 𝔣 B₀ hB₀ i j, p.Prime := by
  intro p hp
  rcases (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j p).mp hp with rfl | rfl | rfl | rfl
  exacts [firstPrimeOf_prime K 𝔣 B₀ hB₀ i, secondPrimeOf_prime K 𝔣 B₀ hB₀ i, firstPrimeOf_prime K 𝔣 B₀ hB₀ j,
    secondPrimeOf_prime K 𝔣 B₀ hB₀ j]

private theorem pairPrimes_notMem : ∀ p ∈ pairPrimes K 𝔣 B₀ hB₀ i j, p ∉ B₀ := by
  intro p hp
  rcases (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j p).mp hp with rfl | rfl | rfl | rfl
  exacts [firstPrimeOf_notMem K 𝔣 B₀ hB₀ i, secondPrimeOf_notMem K 𝔣 B₀ hB₀ i, firstPrimeOf_notMem K 𝔣 B₀ hB₀ j,
    secondPrimeOf_notMem K 𝔣 B₀ hB₀ j]

private theorem firstPrimeOf_mem_pairPrimes_left : firstPrimeOf K 𝔣 B₀ hB₀ i ∈ pairPrimes K 𝔣 B₀ hB₀ i j :=
  (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j _).mpr (Or.inl rfl)
private theorem secondPrimeOf_mem_pairPrimes_left : secondPrimeOf K 𝔣 B₀ hB₀ i ∈ pairPrimes K 𝔣 B₀ hB₀ i j :=
  (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j _).mpr (Or.inr (Or.inl rfl))
private theorem firstPrimeOf_mem_pairPrimes_right : firstPrimeOf K 𝔣 B₀ hB₀ j ∈ pairPrimes K 𝔣 B₀ hB₀ i j :=
  (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j _).mpr (Or.inr (Or.inr (Or.inl rfl)))
private theorem secondPrimeOf_mem_pairPrimes_right : secondPrimeOf K 𝔣 B₀ hB₀ j ∈ pairPrimes K 𝔣 B₀ hB₀ i j :=
  (mem_pairPrimes_iff K 𝔣 B₀ hB₀ i j _).mpr (Or.inr (Or.inr (Or.inr rfl)))

private def pairLevel : ℕ := primeProd (pairPrimes K 𝔣 B₀ hB₀ i j)

private scoped instance neZero_pairLevel : NeZero (pairLevel K 𝔣 B₀ hB₀ i j) :=
  ⟨primeProd_ne_zero _ (pairPrimes_prime K 𝔣 B₀ hB₀ i j)⟩

private theorem primeFactors_pairLevel_notMem : ∀ p ∈ (pairLevel K 𝔣 B₀ hB₀ i j).primeFactors, p ∉ B₀ := by
  rw [pairLevel, primeFactors_primeProd _ (pairPrimes_prime K 𝔣 B₀ hB₀ i j)]
  exact pairPrimes_notMem K 𝔣 B₀ hB₀ i j

private theorem levelOf_dvd_pairLevel (k : ↥(primeCarriers K 𝔣)) (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j)
    (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) : levelOf K 𝔣 B₀ hB₀ k ∣ pairLevel K 𝔣 B₀ hB₀ i j :=
  (coprime_firstPrimeOf_secondPrimeOf K 𝔣 B₀ hB₀ k).mul_dvd_of_dvd_of_dvd (dvd_primeProd _ h1) (dvd_primeProd _ h2)

private scoped instance fact_levelOf_dvd_pairLevel_left : Fact (levelOf K 𝔣 B₀ hB₀ i ∣ pairLevel K 𝔣 B₀ hB₀ i j) :=
  ⟨levelOf_dvd_pairLevel K 𝔣 B₀ hB₀ i j i (firstPrimeOf_mem_pairPrimes_left K 𝔣 B₀ hB₀ i j)
    (secondPrimeOf_mem_pairPrimes_left K 𝔣 B₀ hB₀ i j)⟩

private scoped instance fact_levelOf_dvd_pairLevel_right : Fact (levelOf K 𝔣 B₀ hB₀ j ∣ pairLevel K 𝔣 B₀ hB₀ i j) :=
  ⟨levelOf_dvd_pairLevel K 𝔣 B₀ hB₀ i j j (firstPrimeOf_mem_pairPrimes_right K 𝔣 B₀ hB₀ i j)
    (secondPrimeOf_mem_pairPrimes_right K 𝔣 B₀ hB₀ i j)⟩

private def pairTarget (p : ℕ) : (ZMod p)ˣ :=
  if hp : p.Prime ∧ (p = globalQ B₀ hB₀ ∨ p = globalQ' B₀ hB₀) then @unitGen p ⟨hp.1⟩ else 1

private def pairUnit : (ZMod (pairLevel K 𝔣 B₀ hB₀ i j))ˣ :=
  unitOfTargets (pairPrimes K 𝔣 B₀ hB₀ i j) (pairPrimes_prime K 𝔣 B₀ hB₀ i j) (pairTarget B₀ hB₀)

private theorem unitsMap_pairUnit_firstPrimeOf (k : ↥(primeCarriers K 𝔣)) (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    ZMod.unitsMap (dvd_primeProd _ h1) (pairUnit K 𝔣 B₀ hB₀ i j) = 1 := by
  rw [pairUnit, unitsMap_unitOfTargets _ _ _ h1, pairTarget, dif_neg]
  rintro ⟨-, h | h⟩
  exacts [firstPrimeOf_ne_globalQ K 𝔣 B₀ hB₀ k h, firstPrimeOf_ne_globalQ' K 𝔣 B₀ hB₀ k h]

private theorem unitsMap_pairUnit_secondPrimeOf (k : ↥(primeCarriers K 𝔣)) (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    ZMod.unitsMap (dvd_primeProd _ h2) (pairUnit K 𝔣 B₀ hB₀ i j) = unitGen (secondPrimeOf K 𝔣 B₀ hB₀ k) := by
  rw [pairUnit, unitsMap_unitOfTargets _ _ _ h2, pairTarget, dif_pos ⟨secondPrimeOf_prime K 𝔣 B₀ hB₀ k, secondPrimeOf_mem K 𝔣 B₀ hB₀ k⟩]

end PairLevel
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Gamma

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (𝔣 : Ideal (𝓞 K)) (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) (σ : L ≃ₐ[K] L) (i j : ↥(primeCarriers K 𝔣))
  (hdisj : ∀ (m : ℕ) [NeZero m], (∀ p ∈ m.primeFactors, p ∉ B₀) → Module.finrank K ↥(CycM K L m) = Module.finrank K L * m.totient)

private theorem crtUnits_fst_eq_unitsMap {a b : ℕ} (h : a.Coprime b) [NeZero (a * b)] (u : (ZMod (a * b))ˣ) :
    (crtUnits h u).1 = ZMod.unitsMap (dvd_mul_right a b) u :=
  Units.ext (by rw [val_crtUnits_fst, ZMod.unitsMap_val, ZMod.cast_eq_val])

private theorem crtUnits_snd_eq_unitsMap {a b : ℕ} (h : a.Coprime b) [NeZero (a * b)] (u : (ZMod (a * b))ˣ) :
    (crtUnits h u).2 = ZMod.unitsMap (dvd_mul_left b a) u :=
  Units.ext (by
    rw [show ((crtUnits h u).2 : ZMod b) = (ZMod.cast (u : ZMod (a * b)) : ZMod a × ZMod b).2 from rfl, ZMod.cast_eq_val,
      Prod.snd_natCast, ZMod.unitsMap_val, ZMod.cast_eq_val])

include hdisj in
omit [IsGalois K L] in

private theorem hdeg_pairLevel : Module.finrank K ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j))
    = Module.finrank K ↥(L'M K L (pairLevel K 𝔣 B₀ hB₀ i j)) * (pairLevel K 𝔣 B₀ hB₀ i j).totient := by
  rw [hdisj _ (primeFactors_pairLevel_notMem K 𝔣 B₀ hB₀ i j), ← (toL'M K L (pairLevel K 𝔣 B₀ hB₀ i j)).toLinearEquiv.finrank_eq]

private def pairGamma : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)) ≃ₐ[K] ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)) :=
  (galEquivProd (L'M K L (pairLevel K 𝔣 B₀ hB₀ i j)) (isPrimitiveRoot_ζM K L (pairLevel K 𝔣 B₀ hB₀ i j))
      (MulEquiv.refl ((ZMod (pairLevel K 𝔣 B₀ hB₀ i j))ˣ)) (L'M_sup_adjoin_eq_top K L (pairLevel K 𝔣 B₀ hB₀ i j))
      (hdeg_pairLevel K L 𝔣 B₀ hB₀ i j hdisj)).symm
    ((galEquivL'M K L (pairLevel K 𝔣 B₀ hB₀ i j)).symm σ, pairUnit K 𝔣 B₀ hB₀ i j)

private theorem galProd_pairGamma : galProd (L'M K L (pairLevel K 𝔣 B₀ hB₀ i j)) (isPrimitiveRoot_ζM K L (pairLevel K 𝔣 B₀ hB₀ i j))
      (MulEquiv.refl ((ZMod (pairLevel K 𝔣 B₀ hB₀ i j))ˣ)) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)
    = ((galEquivL'M K L (pairLevel K 𝔣 B₀ hB₀ i j)).symm σ, pairUnit K 𝔣 B₀ hB₀ i j) := by
  rw [← galEquivProd_apply _ _ _ (L'M_sup_adjoin_eq_top K L (pairLevel K 𝔣 B₀ hB₀ i j)) (hdeg_pairLevel K L 𝔣 B₀ hB₀ i j hdisj)]
  exact MulEquiv.apply_symm_apply _ _

private theorem restrict_pairGamma : AlgEquiv.restrictNormalHom (L'M K L (pairLevel K 𝔣 B₀ hB₀ i j)) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)
    = (galEquivL'M K L (pairLevel K 𝔣 B₀ hB₀ i j)).symm σ :=
  congrArg Prod.fst (galProd_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)

private theorem autToPow_pairGamma : (isPrimitiveRoot_ζM K L (pairLevel K 𝔣 B₀ hB₀ i j)).autToPow K (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)
    = pairUnit K 𝔣 B₀ hB₀ i j :=
  congrArg Prod.snd (galProd_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)

variable (k : ↥(primeCarriers K 𝔣)) [hk : Fact (levelOf K 𝔣 B₀ hB₀ k ∣ pairLevel K 𝔣 B₀ hB₀ i j)]

private theorem restrict_resLevel_pairGamma :
    AlgEquiv.restrictNormalHom (L'M K L (levelOf K 𝔣 B₀ hB₀ k)) (resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj))
      = σlevel K L 𝔣 B₀ hB₀ σ k := by
  apply (galEquivL'M K L (levelOf K 𝔣 B₀ hB₀ k)).injective
  rw [galEquivL'M_restrict_resLevel, restrict_pairGamma, σlevel, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem ψlevel_autToPow_resLevel_pairGamma (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j)
    (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    ψlevel K 𝔣 B₀ hB₀ k ((isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ k)).autToPow K
        (resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)))
      = (1, unitGen (secondPrimeOf K 𝔣 B₀ hB₀ k)) := by
  rw [autToPow_resLevel, autToPow_pairGamma]
  haveI : NeZero (firstPrimeOf K 𝔣 B₀ hB₀ k * secondPrimeOf K 𝔣 B₀ hB₀ k) := neZero_levelOf K 𝔣 B₀ hB₀ k
  refine Prod.ext ?_ ?_
  · show (crtUnits (coprime_firstPrimeOf_secondPrimeOf K 𝔣 B₀ hB₀ k) _).1 = 1
    rw [crtUnits_fst_eq_unitsMap]
    show ((ZMod.unitsMap (dvd_mul_right _ _)).comp (ZMod.unitsMap hk.out)) (pairUnit K 𝔣 B₀ hB₀ i j) = 1
    rw [ZMod.unitsMap_comp]
    exact unitsMap_pairUnit_firstPrimeOf K 𝔣 B₀ hB₀ i j k h1
  · show (crtUnits (coprime_firstPrimeOf_secondPrimeOf K 𝔣 B₀ hB₀ k) _).2 = unitGen (secondPrimeOf K 𝔣 B₀ hB₀ k)
    rw [crtUnits_snd_eq_unitsMap]
    show ((ZMod.unitsMap (dvd_mul_left _ _)).comp (ZMod.unitsMap hk.out)) (pairUnit K 𝔣 B₀ hB₀ i j) = _
    rw [ZMod.unitsMap_comp]
    exact unitsMap_pairUnit_secondPrimeOf K 𝔣 B₀ hB₀ i j k h2

private theorem galProd_resLevel_pairGamma (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j)
    (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    galProd (L'M K L (levelOf K 𝔣 B₀ hB₀ k)) (isPrimitiveRoot_ζM K L (levelOf K 𝔣 B₀ hB₀ k)) (ψlevel K 𝔣 B₀ hB₀ k)
        (resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj))
      = (σlevel K L 𝔣 B₀ hB₀ σ k, (1, unitGen (secondPrimeOf K 𝔣 B₀ hB₀ k))) :=
  Prod.ext (restrict_resLevel_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj k) (ψlevel_autToPow_resLevel_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj k h1 h2)

private theorem resLevel_pairGamma_mem_fixingSubgroup [IsMulCommutative (L ≃ₐ[K] L)] (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j)
    (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj) ∈ (Efield K L 𝔣 B₀ hB₀ σ k).fixingSubgroup :=
  mem_fixingSubgroup_auxFieldArtin_of_galProd_eq_gen _ _ _ _ _ _ _ _
    (galProd_resLevel_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj k h1 h2)

private theorem pairGamma_mem_fixingSubgroup_map [IsMulCommutative (L ≃ₐ[K] L)] (h1 : firstPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j)
    (h2 : secondPrimeOf K 𝔣 B₀ hB₀ k ∈ pairPrimes K 𝔣 B₀ hB₀ i j) :
    pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj
      ∈ ((Efield K L 𝔣 B₀ hB₀ σ k).map (inclM K L (levelOf_dvd_pairLevel K 𝔣 B₀ hB₀ i j k h1 h2))).fixingSubgroup := by
  rw [mem_fixingSubgroup_intermediateField_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hfix : resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj) x = x :=
    (mem_fixingSubgroup_intermediateField_iff _ _).mp (resLevel_pairGamma_mem_fixingSubgroup K L 𝔣 B₀ hB₀ σ i j hdisj k h1 h2) x hx
  calc pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj (inclM K L _ x)
      = inclM K L _ (resLevel K L (levelOf K 𝔣 B₀ hB₀ k) (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj) x) :=
        (inclM_resLevel K L (levelOf K 𝔣 B₀ hB₀ k) _ x).symm
    _ = inclM K L _ x := by rw [hfix]

end Gamma
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
  (𝔣 : Ideal (𝓞 K)) (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) (σ : L ≃ₐ[K] L) (i j : ↥(primeCarriers K 𝔣))
  (hdisj : ∀ (m : ℕ) [NeZero m], (∀ p ∈ m.primeFactors, p ∉ B₀) → Module.finrank K ↥(CycM K L m) = Module.finrank K L * m.totient)

set_option synthInstance.maxHeartbeats 1600000

private theorem hiM : levelOf K 𝔣 B₀ hB₀ i ∣ pairLevel K 𝔣 B₀ hB₀ i j := (fact_levelOf_dvd_pairLevel_left K 𝔣 B₀ hB₀ i j).out

private theorem hjM : levelOf K 𝔣 B₀ hB₀ j ∣ pairLevel K 𝔣 B₀ hB₀ i j := (fact_levelOf_dvd_pairLevel_right K 𝔣 B₀ hB₀ i j).out

private abbrev pairE : IntermediateField K ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)) :=
  pairField K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)

private abbrev pairNK : IntermediateField K ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)) :=
  pairN K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)

private theorem pairGamma_mem_fixingSubgroup_pairE :
    pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj ∈ (pairE K L 𝔣 B₀ hB₀ σ i j).fixingSubgroup := by
  rw [pairE, pairField, IntermediateField.fixingSubgroup_sup]
  exact ⟨pairGamma_mem_fixingSubgroup_map K L 𝔣 B₀ hB₀ σ i j hdisj i (firstPrimeOf_mem_pairPrimes_left K 𝔣 B₀ hB₀ i j)
      (secondPrimeOf_mem_pairPrimes_left K 𝔣 B₀ hB₀ i j),
    pairGamma_mem_fixingSubgroup_map K L 𝔣 B₀ hB₀ σ i j hdisj j (firstPrimeOf_mem_pairPrimes_right K 𝔣 B₀ hB₀ i j)
      (secondPrimeOf_mem_pairPrimes_right K 𝔣 B₀ hB₀ i j)⟩

private theorem pairGamma_apply_of_mem {x : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j))} (hx : x ∈ pairE K L 𝔣 B₀ hB₀ σ i j) :
    pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj x = x :=
  (mem_fixingSubgroup_intermediateField_iff _ _).mp (pairGamma_mem_fixingSubgroup_pairE K L 𝔣 B₀ hB₀ σ i j hdisj) x hx

private def pairTauK : ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) ≃ₐ[K] ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) :=
  (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj).restrictNormal ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)

private theorem coe_pairTauK (z : ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)) :
    ((pairTauK K L 𝔣 B₀ hB₀ σ i j hdisj z : ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)) : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)))
      = pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj z :=
  AlgEquiv.restrictNormal_commutes (pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj) ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) z

private theorem coe_algebraMap_pairE (y : ↥(pairE K L 𝔣 B₀ hB₀ σ i j)) :
    ((algebraMap ↥(pairE K L 𝔣 B₀ hB₀ σ i j) ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) y : ↥(pairNK K L 𝔣 B₀ hB₀ σ i j))
        : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j))) = (y : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j))) :=
  IntermediateField.coe_inclusion _ y

private def pairTau : ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) ≃ₐ[↥(pairE K L 𝔣 B₀ hB₀ σ i j)] ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) :=
  AlgEquiv.ofRingEquiv (f := (pairTauK K L 𝔣 B₀ hB₀ σ i j hdisj).toRingEquiv) fun y => Subtype.ext (by
    rw [AlgEquiv.coe_ringEquiv, coe_pairTauK, coe_algebraMap_pairE]
    exact pairGamma_apply_of_mem K L 𝔣 B₀ hB₀ σ i j hdisj y.2)

private theorem restrictScalars_pairTau : (pairTau K L 𝔣 B₀ hB₀ σ i j hdisj).restrictScalars K = pairTauK K L 𝔣 B₀ hB₀ σ i j hdisj :=
  AlgEquiv.ext fun _ => rfl

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem pairGamma_toL'M (a : L) :
    pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj (toL'M K L (pairLevel K 𝔣 B₀ hB₀ i j) a : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)))
      = (toL'M K L (pairLevel K 𝔣 B₀ hB₀ i j) (σ a) : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j))) := by
  have h := congrArg (fun φ => ((φ (toL'M K L (pairLevel K 𝔣 B₀ hB₀ i j) a) : ↥(L'M K L (pairLevel K 𝔣 B₀ hB₀ i j)))
    : ↥(CycM K L (pairLevel K 𝔣 B₀ hB₀ i j)))) (restrict_pairGamma K L 𝔣 B₀ hB₀ σ i j hdisj)
  beta_reduce at h
  rw [AlgEquiv.restrictNormalHom_apply] at h
  rw [h, galEquivL'M, MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

private theorem resHom_pairTau :
    resHom K L ↥(pairE K L 𝔣 B₀ hB₀ σ i j) ↥(pairNK K L 𝔣 B₀ hB₀ σ i j) (pairTau K L 𝔣 B₀ hB₀ σ i j hdisj) = σ := by
  rw [resHom_apply, restrictScalars_pairTau]
  apply AlgEquiv.ext
  intro a
  apply (algebraMap L ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)).injective
  rw [AlgEquiv.restrictNormal_commutes]
  apply Subtype.ext
  rw [coe_pairTauK, algebraMap_L_eq_inclusion_toL'M, algebraMap_L_eq_inclusion_toL'M, IntermediateField.coe_inclusion,
    IntermediateField.coe_inclusion, pairGamma_toL'M]

include hdisj in

private theorem hσ_pair : σ ∈ (resHom K L ↥(pairE K L 𝔣 B₀ hB₀ σ i j) ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)).range :=
  ⟨pairTau K L 𝔣 B₀ hB₀ σ i j hdisj, resHom_pairTau K L 𝔣 B₀ hB₀ σ i j hdisj⟩

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped nonZeroDivisors

section Transitivity

variable (K E E'' : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Field E''] [NumberField E'']
  [Algebra K E] [Algebra K E''] [Algebra E E''] [IsScalarTower K E E'']

private theorem relNormCTM_relNormCTM_cast (𝔣 : Ideal (𝓞 K)) (B : ↥(coprimeToModulus E'' (modulusExt K E'' 𝔣))) :
    relNormCTM K E 𝔣 (relNormCTM E E'' (modulusExt K E 𝔣) ((modulusExt_modulusExt K E E'' 𝔣) ▸ B)) = relNormCTM K E'' 𝔣 B := by
  apply Subtype.ext
  rw [coe_relNormCTM, coe_relNormCTM, coe_relNormCTM, coe_modulusExt_cast E'' (modulusExt_modulusExt K E E'' 𝔣) B,
    ← fracRelNormUnit_comp K E E'']

end Transitivity
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Hcross

variable (K L E N E' E'' N'' : Type*)
  [Field K] [NumberField K] [Field L] [NumberField L] [Field E] [NumberField E] [Field N] [NumberField N]
  [Field E'] [NumberField E'] [Field E''] [NumberField E''] [Field N''] [NumberField N'']

  [Algebra K L] [Algebra K E] [Algebra K N] [Algebra E N] [Algebra L N] [IsScalarTower K E N] [IsScalarTower K L N]
  [IsGalois K L] [IsGalois E N] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (N ≃ₐ[E] N)]

  [Algebra K E'] [Algebra K E''] [Algebra E E''] [Algebra E' E''] [IsScalarTower K E E''] [IsScalarTower K E' E'']

  [Algebra K N''] [Algebra E'' N''] [Algebra L N''] [IsScalarTower K E'' N''] [IsScalarTower K L N'']
  [IsGalois E'' N''] [IsMulCommutative (N'' ≃ₐ[E''] N'')]

end Hcross
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped nonZeroDivisors

section HcrossM

variable (K L E E' E'' N'' : Type*)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
  [Field E] [NumberField E] [Algebra K E] [Field E'] [NumberField E'] [Algebra K E']
  [Field E''] [NumberField E''] [Algebra K E''] [Algebra E E''] [Algebra E' E''] [IsScalarTower K E E''] [IsScalarTower K E' E'']
  [Field N''] [NumberField N''] [Algebra K N''] [Algebra E'' N''] [Algebra L N''] [IsScalarTower K E'' N''] [IsScalarTower K L N'']
  [IsGalois E'' N''] [IsMulCommutative (N'' ≃ₐ[E''] N'')]

private theorem ctmInclusion_ctmInclusion {𝔣 𝔪 𝔪'' : Ideal (𝓞 K)} (h : 𝔣 ∣ 𝔪) (h' : 𝔪 ∣ 𝔪'') (x : ↥(coprimeToModulus K 𝔪'')) :
    ctmInclusion K h (ctmInclusion K h' x) = ctmInclusion K (dvd_trans h h') x :=
  Subtype.ext rfl

private def pushNorm {𝔪 𝔪'' : Ideal (𝓞 K)} (hi : 𝔪 ∣ 𝔪'') (B : ↥(coprimeToModulus E'' (modulusExt K E'' 𝔪''))) :
    ↥(coprimeToModulus E (modulusExt K E 𝔪)) :=
  relNormCTM E E'' (modulusExt K E 𝔪)
    ((modulusExt_modulusExt K E E'' 𝔪) ▸ ctmInclusion E'' (modulusExt_dvd_modulusExt K E'' hi) B)

private theorem ctmInclusion_relNormCTM_pushNorm {𝔣 𝔪 𝔪'' : Ideal (𝓞 K)} (h𝔪 : 𝔣 ∣ 𝔪) (hi : 𝔪 ∣ 𝔪'')
    (B : ↥(coprimeToModulus E'' (modulusExt K E'' 𝔪''))) :
    ctmInclusion K h𝔪 (relNormCTM K E 𝔪 (pushNorm K E E'' hi B))
      = ctmInclusion K (dvd_trans h𝔪 hi) (relNormCTM K E'' 𝔪'' B) := by
  unfold pushNorm
  rw [relNormCTM_relNormCTM_cast K E E'' 𝔪, relNormCTM_ctmInclusion K E'' hi B, ctmInclusion_ctmInclusion]

private theorem hcrossM_of_onto {𝔣 𝔪 𝔪' 𝔪'' : Ideal (𝓞 K)} (h𝔪 : 𝔣 ∣ 𝔪) (h𝔪' : 𝔣 ∣ 𝔪') (hi : 𝔪 ∣ 𝔪'') (hj : 𝔪' ∣ 𝔪'')
    (σ : L ≃ₐ[K] L) (ω : ↥(coprimeToModulus E (modulusExt K E 𝔪)) →* (L ≃ₐ[K] L))
    (hcompat : ∀ x, artinSymbol K L 𝔣 (ctmInclusion K h𝔪 (relNormCTM K E 𝔪 x)) = ω x)
    (hcompat'' : ∀ B, artinSymbol K L 𝔣 (ctmInclusion K (dvd_trans h𝔪 hi) (relNormCTM K E'' 𝔪'' B))
      = resHom K L E'' N'' (artinSymbol E'' N'' (modulusExt K E'' 𝔪'') B))
    (honto'' : Function.Surjective (artinSymbol E'' N'' (modulusExt K E'' 𝔪'')))
    (hσ'' : σ ∈ (resHom K L E'' N'').range) :
    ∃ (b : ↥(coprimeToModulus E (modulusExt K E 𝔪))) (b' : ↥(coprimeToModulus E' (modulusExt K E' 𝔪'))),
      ctmInclusion K h𝔪 (relNormCTM K E 𝔪 b) = ctmInclusion K h𝔪' (relNormCTM K E' 𝔪' b') ∧ ω b = σ := by
  obtain ⟨τ, hτ⟩ := hσ''
  obtain ⟨B, hB⟩ := honto'' τ
  refine ⟨pushNorm K E E'' hi B, pushNorm K E' E'' hj B, ?_, ?_⟩
  · rw [ctmInclusion_relNormCTM_pushNorm, ctmInclusion_relNormCTM_pushNorm]
  · rw [← hcompat, ctmInclusion_relNormCTM_pushNorm, hcompat'', hB, hτ]

end HcrossM
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter WithZero"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem principalIdeles_eq_served : principalIdeles K = M4aHerbrand.principalIdeles (𝓞 K) K := rfl

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter WithZero"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
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

private theorem firstInequalityCTM_of_idele_served (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele K L 𝔣 h𝔣 Nrm hA1 hA2 hA3 (principalIdeles_eq_served K ▸ hH1d)

private theorem firstInequalityCTM_of_idele_admissible (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : IsAdmissibleModulus K L 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele_served K L 𝔣 hadm.1 Nrm hA1 hA2 (hA3 hadm) hH1d

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter IntermediateField"
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

private theorem artinSymbol_surjective_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective_of_firstInequalityCTM 𝔣 fun F hF => by
    obtain ⟨Nrm, h1, h2, h3, h4⟩ := hdata F hF
    exact firstInequalityCTM_intermediateField_of_idele K M F 𝔣 hadm Nrm h1 h2 h3 h4

end Onto
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter IntermediateField"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IntermediateField NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
open LanglandsTunnell.P2.Artin.Ambient
open scoped IsMulCommutative nonZeroDivisors

section Cross

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {σ : L ≃ₐ[K] L}

private theorem honto_of_pairCore {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i} {cj : ArtinFieldCore K L 𝔣 j}
    (P : ArtinPairCore K L 𝔣 σ ci cj)
    (hdata : ∀ F : IntermediateField P.E'' P.N'', (Module.finrank P.E'' F).Prime →
      IdeleFirstIneqData P.E'' P.N'' F (modulusExt K P.E'' P.𝔪'')) :
    Function.Surjective (artinSymbol P.E'' P.N'' (modulusExt K P.E'' P.𝔪'')) :=
  artinSymbol_surjective_of_ideleData P.E'' P.N'' (modulusExt K P.E'' P.𝔪'') P.hadm'' hdata

private theorem hcross_of_pairCore (D : ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore K L 𝔣 i)
    (P : ∀ i j : ↥(primeCarriers K 𝔣), ArtinPairCore K L 𝔣 σ (D i) (D j))
    (hdata_ij : ∀ i j, ∀ F : IntermediateField (P i j).E'' (P i j).N'', (Module.finrank (P i j).E'' F).Prime →
      IdeleFirstIneqData (P i j).E'' (P i j).N'' F (modulusExt K (P i j).E'' (P i j).𝔪'')) :
    ∀ i j : ↥(primeCarriers K 𝔣),
      ∃ (b : (D i).Ip) (b' : (D j).Ip), (D i).Ni b = (D j).Ni b' ∧ (D i).ωpi b = σ := by
  intro i j
  obtain ⟨b, b', h1, h2⟩ := hcrossM_of_onto K L (D i).E (D j).E (P i j).E'' (P i j).N''
    (D i).h𝔪 (D j).h𝔪 (P i j).hi'' (P i j).hj'' σ (D i).ωpi (hcompat_of_core (D i)) (P i j).hcompat''
    (honto_of_pairCore (P i j) (hdata_ij i j)) (P i j).hσ''
  exact ⟨b, b', h1, h2⟩

private theorem isCyclic_of_pairCore [IsCyclic (L ≃ₐ[K] L)] {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i}
    {cj : ArtinFieldCore K L 𝔣 j} (P : ArtinPairCore K L 𝔣 σ ci cj) : IsCyclic (P.N'' ≃ₐ[P.E''] P.N'') :=
  isCyclic_of_injective (resHom K L P.E'' P.N'') P.hresInj''

private theorem isCyclic_of_core [IsCyclic (L ≃ₐ[K] L)] {i : ↥(primeCarriers K 𝔣)} (c : ArtinFieldCore K L 𝔣 i) :
    IsCyclic (c.N ≃ₐ[c.E] c.N) :=
  isCyclic_of_injective (resHom K L c.E c.N) c.hresInj

end Cross
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Family

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
  (𝔣 : Ideal (𝓞 K)) (B₀ : Finset ℕ) (hB₀ : ∀ p ∈ B₀, p.Prime) (σ : L ≃ₐ[K] L) (i j : ↥(primeCarriers K 𝔣))
  (hdisj : ∀ (m : ℕ) [NeZero m], (∀ p ∈ m.primeFactors, p ∉ B₀) → Module.finrank K ↥(CycM K L m) = Module.finrank K L * m.totient)

set_option synthInstance.maxHeartbeats 1600000

private abbrev pairModulus : Ideal (𝓞 K) := modulus K 𝔣 B₀ hB₀ i * Ideal.span {(levelOf K 𝔣 B₀ hB₀ j : 𝓞 K)}

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
omit L [NumberField L] [Algebra K L] in
private theorem dvd_pairModulus : 𝔣 ∣ pairModulus K 𝔣 B₀ hB₀ i j := (dvd_modulus K 𝔣 B₀ hB₀ i).trans (dvd_mul_right _ _)

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
omit L [NumberField L] [Algebra K L] in
private theorem modulus_dvd_pairModulus_left : modulus K 𝔣 B₀ hB₀ i ∣ pairModulus K 𝔣 B₀ hB₀ i j := dvd_mul_right _ _

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
omit L [NumberField L] [Algebra K L] in
private theorem modulus_dvd_pairModulus_right : modulus K 𝔣 B₀ hB₀ j ∣ pairModulus K 𝔣 B₀ hB₀ i j :=
  ⟨Ideal.span {(levelOf K 𝔣 B₀ hB₀ i : 𝓞 K)}, by rw [pairModulus, modulus, modulus, mul_right_comm]⟩

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in
omit L [NumberField L] [Algebra K L] in
private theorem pairModulus_ne_bot (h𝔣 : 𝔣 ≠ ⊥) : pairModulus K 𝔣 B₀ hB₀ i j ≠ ⊥ :=
  mul_ne_zero (modulus_ne_bot K 𝔣 B₀ hB₀ i h𝔣) (fun h => levelOf_ne_zero K 𝔣 B₀ hB₀ j (by
    have h' : Ideal.span {(levelOf K 𝔣 B₀ hB₀ j : 𝓞 K)} = ⊥ := h
    rwa [Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h'))

private def artinPairCore_of (h𝔣 : IsAdmissibleModulus K L 𝔣) (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) :
    ArtinPairCore K L 𝔣 σ (artinFieldCoreFamily K L 𝔣 B₀ hB₀ σ h𝔣 hexp i) (artinFieldCoreFamily K L 𝔣 B₀ hB₀ σ h𝔣 hexp j) where
  E'' := ↥(pairE K L 𝔣 B₀ hB₀ σ i j)
  N'' := ↥(pairNK K L 𝔣 B₀ hB₀ σ i j)
  instNFE := numberField_pairField K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
  instNFN := numberField_pairN K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
  instAiE := algPairI K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
  instAjE := algPairJ K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
  instSTKiE := isScalarTower_pairI K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i)
    (Efield K L 𝔣 B₀ hB₀ σ j)
  instSTKjE := isScalarTower_pairJ K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i)
    (Efield K L 𝔣 B₀ hB₀ σ j)
  instAEN := instAlgEN K L _ _
  instALN := instAlgLN K L _ _
  instSTKEN := instSTKEN K L _ _
  instSTKLN := instSTKLN K L _ _
  instGEN := isGalois_pairEN K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
  instCN := isMulCommutative_galPairEN K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i)
    (Efield K L 𝔣 B₀ hB₀ σ j)
  𝔪'' := pairModulus K 𝔣 B₀ hB₀ i j
  h'' := dvd_pairModulus K 𝔣 B₀ hB₀ i j
  hi'' := modulus_dvd_pairModulus_left K 𝔣 B₀ hB₀ i j
  hj'' := modulus_dvd_pairModulus_right K 𝔣 B₀ hB₀ i j
  hadm'' := hadm_pair K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
    h𝔣 (dvd_pairModulus K 𝔣 B₀ hB₀ i j) (pairModulus_ne_bot K 𝔣 B₀ hB₀ i j (ne_bot_of_isAdmissibleModulus K L h𝔣))
  hcompat'' := hcompat_pair K L (hiM K 𝔣 B₀ hB₀ i j) (hjM K 𝔣 B₀ hB₀ i j) (Efield K L 𝔣 B₀ hB₀ σ i) (Efield K L 𝔣 B₀ hB₀ σ j)
    h𝔣 (dvd_pairModulus K 𝔣 B₀ hB₀ i j)
  hσ'' := hσ_pair K L 𝔣 B₀ hB₀ σ i j hdisj
  hresInj'' := resHom_injective_sup_L K L (pairLevel K 𝔣 B₀ hB₀ i j) (pairE K L 𝔣 B₀ hB₀ σ i j)

private def artinPairCoreFamily (h𝔣 : IsAdmissibleModulus K L 𝔣) (hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1) :
    ∀ i j : ↥(primeCarriers K 𝔣),
      ArtinPairCore K L 𝔣 σ (artinFieldCoreFamily K L 𝔣 B₀ hB₀ σ h𝔣 hexp i) (artinFieldCoreFamily K L 𝔣 B₀ hB₀ σ h𝔣 hexp j) :=
  fun i j => artinPairCore_of K L 𝔣 B₀ hB₀ σ i j hdisj h𝔣 hexp

end Family
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

private abbrev GL23 : Type := GL (Fin 2) (ZMod 3)

section GLCore

end GLCore
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Lattice

variable {Γ : Type*} [Group Γ] (π : Γ →* GL23)

variable (hπ : Function.Surjective π)
include hπ

end Lattice
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField Polynomial

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (e : (L ≃ₐ[ℚ] L) ≃* GL23)

private scoped instance (priority := high) isCyclotomicExtension_cyclotomicField_rat (k : ℕ) : IsCyclotomicExtension {k} ℚ (CyclotomicField k ℚ) := by
  convert (inferInstance : @IsCyclotomicExtension {k} ℚ (CyclotomicField k ℚ) _ _ (CyclotomicField.algebra k ℚ)) <;>
    exact Subsingleton.elim _ _

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

open IntermediateField Polynomial

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (e : (L ≃ₐ[ℚ] L) ≃* GL23)

@[reducible] private def algQL : Algebra ℚ L := DivisionRing.toRatAlgebra

section Abstract
variable {N : Type*} [Field N] [Algebra ℚ N] [FiniteDimensional ℚ N] [IsGalois ℚ N]

attribute [local instance] algQL
p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

variable (L_N : IntermediateField ℚ N) [IsGalois ℚ L_N] (ι : L ≃ₐ[ℚ] ↥L_N)

section Bridge

variable {M : ℕ} [NeZero M] {ξ : N} (hξ : IsPrimitiveRoot ξ M)
include hξ

end Bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end Abstract
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section ed19Prints
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end ed19Prints
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

open IntermediateField Polynomial LanglandsTunnell.P2.Artin.Ambient

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (e : (L ≃ₐ[ℚ] L) ≃* GL23)
variable (K : Type*) [Field K] [NumberField K] [Algebra K L] [IsGalois K L]

@[reducible] private def algQK : Algebra ℚ K := DivisionRing.toRatAlgebra

section Level

variable (m : ℕ) [NeZero m]

attribute [local instance] algQL algQK
p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

private scoped instance instSTQKL : IsScalarTower ℚ K L :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

omit [IsGalois ℚ L] [NumberField K] [IsGalois K L] in

private theorem algebraMap_K_mem_L'Q (a : K) : algebraMap K (Ω L) a ∈ L' ℚ L := by
  rw [IsScalarTower.algebraMap_apply K L (Ω L)]
  exact ⟨algebraMap K L a, rfl⟩

omit [IsGalois ℚ L] [IsGalois K L] in

private theorem restrictScalars_cycM_eq :
    (CycM K L m).restrictScalars ℚ = CycM ℚ L m := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  ·
    show ((CycM K L m).restrictScalars ℚ).toSubfield ≤ (CycM ℚ L m).toSubfield
    simp only [IntermediateField.restrictScalars_toSubfield]
    show (CycM K L m).toSubfield ≤ _
    rw [CycM, sup_def, adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (Set.union_subset ?_ ?_))
    · exact fun x ⟨a, ha⟩ => (le_sup_left : L' ℚ L ≤ CycM ℚ L m) (ha ▸ algebraMap_K_mem_L'Q K a)
    · rintro x ⟨a, rfl⟩
      exact (le_sup_left : L' ℚ L ≤ CycM ℚ L m) ⟨a, rfl⟩
    ·
      show ((adjoin K {ζΩ L m} : IntermediateField K (Ω L)) : Set (Ω L)) ⊆ CycM ℚ L m
      rw [show ((adjoin K {ζΩ L m} : IntermediateField K (Ω L)) : Set (Ω L))
        = ((adjoin K {ζΩ L m}).toSubfield : Set (Ω L)) from rfl, adjoin_toSubfield]
      refine Subfield.closure_le.mpr (Set.union_subset ?_ ?_)
      · exact fun x ⟨a, ha⟩ => (le_sup_left : L' ℚ L ≤ CycM ℚ L m) (ha ▸ algebraMap_K_mem_L'Q K a)
      · exact fun x hx => (le_sup_right : adjoin ℚ {ζΩ L m} ≤ CycM ℚ L m)
          (IntermediateField.subset_adjoin ℚ _ hx)
  · intro x ⟨a, ha⟩
    exact le_sup_left (a := L' K L) (ha ▸ ⟨a, rfl⟩)
  · exact adjoin_le_iff.mpr fun x hx =>
      le_sup_right (a := L' K L) (IntermediateField.subset_adjoin K _ hx)

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section ed19Prints
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end ed19Prints
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

noncomputable section

p2m_open "Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField IsDedekindDomain"
open scoped nonZeroDivisors IsMulCommutative Pointwise

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section SupplierDock

universe u

variable {L : Type u} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

local notation "K'" => (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)

end SupplierDock
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section ed19Prints
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"
end ed19Prints
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section

set_option autoImplicit false

p2m_open "NumberField P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.NumberField Deep.NTSupply P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.Deep.NTSupply"
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin"

universe u v

section

set_option autoImplicit false

noncomputable section

open IntermediateField Polynomial LanglandsTunnell.P2.Artin.Ambient

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {L : Type*} [Field L] [NumberField L]

private def disjBadPrimes : Finset ℕ := (NumberField.discr L).natAbs.primeFactors

private theorem disjBadPrimes_prime {p : ℕ} (hp : p ∈ disjBadPrimes (L := L)) : p.Prime :=
  Nat.prime_of_mem_primeFactors hp

private theorem disj_coprime_of_avoid (m : ℕ) [NeZero m]
    (havoid : ∀ p ∈ m.primeFactors, p ∉ disjBadPrimes (L := L)) :
    Nat.Coprime m (NumberField.discr L).natAbs := by
  refine Nat.coprime_of_dvd' fun p hp hpm hpd => ?_
  have hd0 : (NumberField.discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)
  exact absurd (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩)
    (havoid p (Nat.mem_primeFactors.mpr ⟨hp, hpm, NeZero.ne m⟩))

section Level

variable (m : ℕ) [NeZero m]

attribute [local instance] algQL
p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

private theorem disj_isCyclotomic_adjoin :
    IsCyclotomicExtension {m} ℚ (IntermediateField.adjoin ℚ {ζM ℚ L m}) :=
  (isPrimitiveRoot_ζM ℚ L m).intermediateField_adjoin_isCyclotomicExtension ℚ

private theorem disj_isCoprime_discr
    (havoid : ∀ p ∈ m.primeFactors, p ∉ disjBadPrimes (L := L)) :
    IsCoprime (NumberField.discr (IntermediateField.adjoin ℚ {ζM ℚ L m}))
      (NumberField.discr (L'M ℚ L m)) := by
  haveI := disj_isCyclotomic_adjoin (L := L) m
  have hcyc := IsCyclotomicExtension.Rat.natAbs_discr (K := IntermediateField.adjoin ℚ {ζM ℚ L m}) (n := m)
  have himg : NumberField.discr (L'M ℚ L m) = NumberField.discr L :=
    (NumberField.discr_eq_discr_of_algEquiv L (toL'M ℚ L m)).symm
  rw [Int.isCoprime_iff_nat_coprime, hcyc, himg]
  refine Nat.Coprime.coprime_div_left ?_
    (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos m))
  exact Nat.Coprime.pow_left _ (disj_coprime_of_avoid (L := L) m havoid)

private theorem disj_linearDisjoint
    (havoid : ∀ p ∈ m.primeFactors, p ∉ disjBadPrimes (L := L)) :
    (L'M ℚ L m).LinearDisjoint (IntermediateField.adjoin ℚ {ζM ℚ L m}) := by
  haveI := disj_isCyclotomic_adjoin (L := L) m
  haveI : IsGalois ℚ (IntermediateField.adjoin ℚ {ζM ℚ L m}) := IsCyclotomicExtension.isGalois {m} ℚ _
  exact (NumberField.linearDisjoint_of_isGalois_isCoprime_discr _ (IntermediateField.adjoin ℚ {ζM ℚ L m})
    (L'M ℚ L m) (disj_isCoprime_discr (L := L) m havoid)).symm

private theorem disj_finrank_cycMQ
    (havoid : ∀ p ∈ m.primeFactors, p ∉ disjBadPrimes (L := L)) :
    Module.finrank ℚ ↥(CycM ℚ L m) = Module.finrank ℚ L * m.totient := by
  haveI := disj_isCyclotomic_adjoin (L := L) m
  have hζ : Module.finrank ℚ (IntermediateField.adjoin ℚ {ζM ℚ L m}) = m.totient :=
    IsCyclotomicExtension.Rat.finrank m _

  have h : Module.finrank ℚ ↥(L'M ℚ L m ⊔ IntermediateField.adjoin ℚ {ζM ℚ L m})
      = Module.finrank ℚ ↥(L'M ℚ L m) * Module.finrank ℚ ↥(IntermediateField.adjoin ℚ {ζM ℚ L m}) :=
    (disj_linearDisjoint (L := L) m havoid).finrank_sup
  have hsup : Module.finrank ℚ ↥(L'M ℚ L m ⊔ IntermediateField.adjoin ℚ {ζM ℚ L m})
      = Module.finrank ℚ ↥(CycM ℚ L m) :=
    (congrArg (fun S : IntermediateField ℚ (CycM ℚ L m) => Module.finrank ℚ ↥S)
      (L'M_sup_adjoin_eq_top ℚ L m)).trans IntermediateField.finrank_top'
  have hL : Module.finrank ℚ ↥(L'M ℚ L m) = Module.finrank ℚ L :=
    (toL'M ℚ L m).toLinearEquiv.finrank_eq.symm
  rw [← hsup, h, hL, hζ]

variable (K : Type*) [Field K] [NumberField K] [Algebra K L]

attribute [local instance] algQK

private theorem disj_finrank_cycM
    (havoid : ∀ p ∈ m.primeFactors, p ∉ disjBadPrimes (L := L)) :
    Module.finrank K ↥(CycM K L m) = Module.finrank K L * m.totient := by
  have hQ := disj_finrank_cycMQ (L := L) m havoid
  have htwr1 : Module.finrank ℚ K * Module.finrank K ↥(CycM K L m)
      = Module.finrank ℚ ↥(CycM K L m) := Module.finrank_mul_finrank ℚ K ↥(CycM K L m)
  have htwr2 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ K L
  have hcarr : Module.finrank ℚ ↥(CycM K L m) = Module.finrank ℚ ↥(CycM ℚ L m) := by
    have := restrictScalars_cycM_eq K (L := L) m
    exact this ▸ rfl
  have hK0 : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have : Module.finrank ℚ K * Module.finrank K ↥(CycM K L m)
      = Module.finrank ℚ K * (Module.finrank K L * m.totient) := by
    rw [htwr1, hcarr, hQ, ← htwr2, mul_assoc]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hK0) this

end Level
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

private theorem disj_exists_badPrimes (K : Type*) [Field K] [NumberField K] [Algebra K L] :
    ∃ B₀ : Finset ℕ, (∀ p ∈ B₀, p.Prime) ∧
      ∀ (m : ℕ) [NeZero m], (∀ p ∈ m.primeFactors, p ∉ B₀) →
        Module.finrank K ↥(CycM K L m) = Module.finrank K L * m.totient :=
  ⟨disjBadPrimes (L := L), fun _ hp => disjBadPrimes_prime hp,
    fun m _ havoid => disj_finrank_cycM (L := L) m K havoid⟩

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

namespace LanglandsTunnell
namespace P2
p2m_export "LanglandsTunnell.P2" "c8H"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers ctmInclusion resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles ArtinFieldCore ArtinPairCore IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "IsDedekindDomain HeckeCharacter P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section ATDGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

private theorem atd_card_gal (h2 : Module.finrank K L = 2) : Nat.card (L ≃ₐ[K] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, h2]

private theorem atd_hexp (h2 : Module.finrank K L = 2) (x : L ≃ₐ[K] L) : x ^ 8 = 1 := by
  have hx : x ^ 2 = 1 := by
    rw [← atd_card_gal h2]
    exact pow_card_eq_one'
  calc x ^ 8 = (x ^ 2) ^ 4 := by rw [← pow_mul]
    _ = 1 := by rw [hx, one_pow]

end ATDGroup
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

section ATDGlue

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

private theorem atd_exists_card_eq_two_pow_of_core (h2 : Module.finrank K L = 2) {𝔣 : Ideal (𝓞 K)}
    {i : ↥(primeCarriers K 𝔣)} (c : ArtinFieldCore K L 𝔣 i) :
    ∃ m : ℕ, Nat.card (c.N ≃ₐ[c.E] c.N) = 2 ^ m := by
  have hdvd := Subgroup.card_dvd_of_injective _ c.hresInj
  rw [atd_card_gal h2] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private theorem atd_exists_card_eq_two_pow_of_pairCore (h2 : Module.finrank K L = 2) {𝔣 : Ideal (𝓞 K)}
    {σ : L ≃ₐ[K] L} {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i} {cj : ArtinFieldCore K L 𝔣 j}
    (P : ArtinPairCore K L 𝔣 σ ci cj) :
    ∃ m : ℕ, Nat.card (P.N'' ≃ₐ[P.E''] P.N'') = 2 ^ m := by
  have hdvd := Subgroup.card_dvd_of_injective _ P.hresInj''
  rw [atd_card_gal h2] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private theorem atd_hCSb (h2 : Module.finrank K L = 2) {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i) : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪) := by
  obtain ⟨m, hm⟩ := atd_exists_card_eq_two_pow_of_core h2 c
  exact secondInequalityCTM_of_kummer c.E c.N _ (M4aKummer.normClassIndex_dvd_card_aut c.E c.N m hm _)

private theorem atd_hFI (h2 : Module.finrank K L = 2) {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i) :
    ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime →
      FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪) := by
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd_card_gal h2)
  refine firstInequalityCTM_prime_of_ideleData c.E c.N _ c.hadm ?_
  intro F hprime
  haveI := isCyclic_of_core c
  obtain ⟨m, hm⟩ := atd_exists_card_eq_two_pow_of_core h2 c
  haveI := isGalois_intermediateField (K := c.E) (M := c.N) F
  haveI := isCyclic_intermediateField (K := c.E) (M := c.N) F
  exact (ideleFirstIneqData_iff_at c.E c.N F _).mpr
    (HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic c.E F
      (finrank_intermediateField_dvd_twentyFour hm F hprime) _)

private theorem atd_hdata_pair (h2 : Module.finrank K L = 2) {𝔣 : Ideal (𝓞 K)} {σ : L ≃ₐ[K] L}
    {i j : ↥(primeCarriers K 𝔣)} {ci : ArtinFieldCore K L 𝔣 i} {cj : ArtinFieldCore K L 𝔣 j}
    (P : ArtinPairCore K L 𝔣 σ ci cj) :
    ∀ F : IntermediateField P.E'' P.N'', (Module.finrank P.E'' F).Prime →
      IdeleFirstIneqData P.E'' P.N'' F (modulusExt K P.E'' P.𝔪'') := by
  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd_card_gal h2)
  intro F hprime
  haveI := isCyclic_of_pairCore P
  obtain ⟨m, hm⟩ := atd_exists_card_eq_two_pow_of_pairCore h2 P
  haveI := isGalois_intermediateField (K := P.E'') (M := P.N'') F
  haveI := isCyclic_intermediateField (K := P.E'') (M := P.N'') F
  exact (ideleFirstIneqData_iff_at P.E'' P.N'' F _).mpr
    (HeckeCharacter.ideleFirstIneqDataAt_of_isCyclic P.E'' F
      (finrank_intermediateField_dvd_twentyFour hm F hprime) _)

end ATDGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (h2 : Module.finrank K L = 2) (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) :
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

  haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (atd_card_gal h2)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hexp : ∀ x : L ≃ₐ[K] L, x ^ 8 = 1 := atd_hexp h2

  obtain ⟨B₀, hB₀, hdisj⟩ := disj_exists_badPrimes (L := L) K

  let D : ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore K L 𝔣 i := artinFieldCoreFamily K L 𝔣 B₀ hB₀ σ hadm hexp
  have hcross : ∀ i j : ↥(primeCarriers K 𝔣),
      ∃ (b : (D i).Ip) (b' : (D j).Ip), (D i).Ni b = (D j).Ni b' ∧ (D i).ωpi b = σ :=
    hcross_of_pairCore D (artinPairCoreFamily K L 𝔣 B₀ hB₀ σ hdisj hadm hexp)
      (fun i j => atd_hdata_pair h2 (artinPairCoreFamily K L 𝔣 B₀ hB₀ σ hdisj hadm hexp i j))

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
    exact hker_of_core (D ⟨p, hp⟩) (atd_hCSb h2 _) (atd_hFI h2 _) _ hx
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
end
p2m_reactivate "P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.M4aP2 P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.LanglandsTunnell.P2.Artin.Ambient"

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two (solution)
