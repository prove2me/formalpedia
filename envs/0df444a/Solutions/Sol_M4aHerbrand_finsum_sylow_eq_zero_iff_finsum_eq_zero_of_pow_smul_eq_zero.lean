-- Prove2me | solution 1 for M4aHerbrand.finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ff26b696-63b4-539c-b6de-b9744eeb7c2a

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_finsum_div_natCard_decomp_eq_finrank_smul_finsum
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart IdeleGaloisDescent injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles exists_hom_res_infPlaceDecomp_ideles_localUnits_apply"
namespace SylowSumProof
p2m_open "M4aHerbrand"

theorem coe_div_eq_zero_of_dvd (n : ℤ) {N : ℕ} (hN : 0 < N) (h : (N : ℤ) ∣ n) :
    ((((n : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨c, ?_⟩
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [zsmul_eq_mul, mul_one, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ hN']

theorem nsmul_eq_zero_iff_of_coprime {M : Type} [AddCommGroup M] (s : M) {a b : ℕ} (hab : Nat.Coprime a b) (ha : a • s = 0) :
    b • s = 0 ↔ s = 0 := by
  refine ⟨fun hb => ?_, fun h => by rw [h, smul_zero]⟩
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hab)
  have h1 : ((u * a + v * b : ℤ)) • s = s := by rw [huv, one_zsmul]
  rw [← h1, add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ha, hb, zsmul_zero, zsmul_zero, add_zero]

end M4aHerbrand.SylowSumProof

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L v))
    (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v))
    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hn : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v))
    (k : ℕ) (hxk : (p ^ k : ℤ) • x = 0) :
    (∑ᶠ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))),
        ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = 0 ↔
      (∑ᶠ v : HeightOneSpectrum (𝓞 E),
        ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = 0 := by
  classical
  rename_i hq hLfd iMS iMD hQ hU hΦ hKfd hB hθ hu
  have hp : p.Prime := Fact.out

  set f : HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ) := fun v =>
    ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) with hf

  have hord : ∀ (v : HeightOneSpectrum (𝓞 E)) (m : ℤ),
      m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v) = 0 ↔
        (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℤ) ∣ m := by
    intro v m
    haveI := hq v; haveI := hLfd v; letI := iMS v; letI := iMD v; haveI := hKfd v
    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (L v) :=
      ⟨fun {g₁} {g₂} hg₁₂ => by
        haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above E F v)
        refine FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above E F v).adicCompletion F) fun yy => (Φ v).injective ?_
        rw [hΦ, hΦ, hg₁₂]⟩
    have hsolv := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (q v) (L v) _ (hQ v)
    exact NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass E F
      (NumberField.PlaceAbove.above E F v) hsolv (q v) (L v) (Φ v) (hQ v) (hU v) (hΦ v) (K₀ v) (hB v) (θ v) (hθ v) (u v) (hu v) m

  have hdvd : ∀ v, (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℤ) ∣ (p ^ k : ℤ) * n v := by
    intro v
    rw [← hord v]
    rw [mul_smul, ← hn v, ← map_zsmul, hxk, map_zero]

  have hfk : ∀ v, p ^ k • f v = 0 := fun v => by
    rw [hf]
    dsimp only
    rw [← natCast_zsmul, ← AddCircle.coe_zsmul, zsmul_eq_mul, ← mul_div_assoc]
    have := M4aHerbrand.SylowSumProof.coe_div_eq_zero_of_dvd ((p ^ k : ℤ) * n v) Nat.card_pos (hdvd v)
    push_cast at this ⊢
    exact this

  have hfin : (Function.support f).Finite := by
    obtain ⟨prInf, hprInf⟩ := M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply E F D hactI
    have hFIN := (M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
      E F D hactI prG hprG prInf hprInf 1).2.1 x
    have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 E) => NumberField.PlaceAbove.above E F v)
        ((fun v => NumberField.PlaceAbove.above E F v) ⁻¹'
          {w : HeightOneSpectrum (𝓞 F) | (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (prG w) (1 + 1)).hom x ≠ 0}) := by
      intro a _ b _ hab
      have := congrArg (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 E)) hab
      simpa only [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, NumberField.PlaceAbove.comap_above] using this
    refine (hFIN.preimage hinj).subset fun v hv => ?_
    rw [Function.mem_support] at hv
    rw [Set.mem_preimage, Set.mem_setOf_eq]
    change (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x ≠ 0
    rw [hn v]
    intro h0
    apply hv
    rw [hf]
    exact M4aHerbrand.SylowSumProof.coe_div_eq_zero_of_dvd _ Nat.card_pos ((hord v (n v)).1 h0)

  rw [NumberField.PlaceDecomp.finsum_div_natCard_decomp_eq_finrank_smul_finsum E F
    (IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) n hfin]
  change Module.finrank E ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) • (∑ᶠ v, f v) = 0 ↔ (∑ᶠ v, f v) = 0

  have hsum : p ^ k • (∑ᶠ v, f v) = 0 := by
    have h1 := (DistribMulAction.toAddMonoidHom (AddCircle (1 : ℚ)) (p ^ k)).map_finsum hfin
    simp only [DistribMulAction.toAddMonoidHom_apply] at h1
    rw [h1]
    exact (finsum_congr hfk).trans finsum_zero
  have hdeg : Module.finrank E ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) = (P : Subgroup (F ≃ₐ[E] F)).index := by
    have h1 := Module.finrank_mul_finrank E ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank E F, ← (P : Subgroup (F ≃ₐ[E] F)).index_mul_card] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [hdeg]
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup (F ≃ₐ[E] F)).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 P.not_dvd_index)
  exact M4aHerbrand.SylowSumProof.nsmul_eq_zero_iff_of_coprime _ hcop hsum

end S_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
end P2MW
export P2MW.S_M4aHerbrand_finsum_sylow_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero (solution)
