-- Prove2me | solution 1 for NumberField.AdeleRing.exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/196a9967-96ea-5719-9b83-d0d49cf1d2cf

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_AdeleRing_mem_unitIdelesOutside_iff_forall_valued_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_valued_snd_smul_smul_eq
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_valued_snd_ne_one
import Theorems.Thm_NumberField_AdeleRing_exists_units_forall_valued_snd_eq_ofAdd_neg
import Theorems.Thm_groupCohomology_exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory groupCohomology
open scoped NumberField.PlaceTransport

set_option maxHeartbeats 3200000 in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (c : (K ≃ₐ[E] K) → (AdeleRing (𝓞 K) K)ˣ)
    (hc : ∀ g h : K ≃ₐ[E] K, c g * (g • c h) / c (g * h) ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) :
    ∃ q : (AdeleRing (𝓞 K) K)ˣ, ∀ g : K ≃ₐ[E] K,
      c g * (g • q / q)⁻¹ ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
  classical

  let val : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → WithZero (Multiplicative ℤ) := fun x w => Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w)
  have hval : ∀ x w, val x w = Valued.v (((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) w) := fun _ _ => rfl
  have hvmul : ∀ (x y : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)), val (x * y) w = val x w * val y w := fun x y w => by
    rw [hval, hval, hval, ← map_mul]; rfl
  have hv1 : ∀ w : HeightOneSpectrum (𝓞 K), val 1 w = 1 := fun w => by rw [hval]; exact map_one _
  have hvne : ∀ (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)), val x w ≠ 0 := fun x w h => by
    have := hvmul x x⁻¹ w
    rw [mul_inv_cancel, hv1, h, zero_mul] at this
    exact one_ne_zero this
  have hvinv : ∀ (x : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)), val x⁻¹ w = (val x w)⁻¹ := fun x w => by
    have := hvmul x x⁻¹ w
    rw [mul_inv_cancel, hv1] at this
    exact (inv_eq_of_mul_eq_one_right this.symm).symm
  have hvdiv : ∀ (x y : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)), val (x / y) w = val x w / val y w := fun x y w => by
    rw [div_eq_mul_inv, hvmul, hvinv, div_eq_mul_inv]

  have hmem := NumberField.AdeleRing.mem_unitIdelesOutside_iff_forall_valued_snd_eq_one K {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) ∈ S}
  have hsm := NumberField.AdeleRing.valued_snd_smul_smul_eq E K D hactI

  let lg : WithZero (Multiplicative ℤ) → ℤ := fun v => if h : v = 0 then 0 else Multiplicative.toAdd (WithZero.unzero h)
  have hlg : ∀ {v : WithZero (Multiplicative ℤ)}, v ≠ 0 → ((Multiplicative.ofAdd (lg v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v := by
    intro v hv; simp only [lg, dif_neg hv, ofAdd_toAdd, WithZero.coe_unzero]
  have hlg_mul : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → b ≠ 0 → lg (a * b) = lg a + lg b := by
    intro a b ha hb
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    apply Multiplicative.ofAdd.injective
    apply WithZero.coe_injective
    rw [ofAdd_add, WithZero.coe_mul, hlg hab, hlg ha, hlg hb]
  have hlg_eq_zero : ∀ {v : WithZero (Multiplicative ℤ)}, v ≠ 0 → (lg v = 0 ↔ v = 1) := by
    intro v hv
    constructor
    · intro h; rw [← hlg hv, h]; rfl
    · intro h; subst h; apply Multiplicative.ofAdd.injective; apply WithZero.coe_injective; rw [hlg one_ne_zero]; rfl

  have hfin := NumberField.AdeleRing.finite_setOf_valued_snd_ne_one K
  let nv : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) →₀ ℤ := fun x => Finsupp.onFinset (hfin x).toFinset
    (fun w => if w.under (𝓞 E) ∈ S then 0 else lg (val x w)) (fun w hw => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_cases hS : w.under (𝓞 E) ∈ S
      · simp [hS] at hw
      · simp only [hS, if_false] at hw
        intro h1; exact hw ((hlg_eq_zero (hvne x w)).2 h1))
  have hnv : ∀ x w, nv x w = if w.under (𝓞 E) ∈ S then 0 else lg (val x w) := fun _ _ => rfl

  have hmd : ∀ (g : (K ≃ₐ[E] K)) (φ : HeightOneSpectrum (𝓞 K) →₀ ℤ) (w : HeightOneSpectrum (𝓞 K)), Finsupp.mapDomain (g • ·) φ w = φ (g⁻¹ • w) := fun g φ w => by
    conv_lhs => rw [← smul_inv_smul g w]
    exact Finsupp.mapDomain_apply (MulAction.injective g) φ (g⁻¹ • w)

  have hcoc : ∀ g h : (K ≃ₐ[E] K), nv (c (g * h)) = nv (c g) + Finsupp.mapDomain (g • ·) (nv (c h)) := by
    intro g h
    ext w
    rw [Finsupp.add_apply, hmd, hnv, hnv, hnv, NumberField.PlaceTransport.under_smul]
    by_cases hS : w.under (𝓞 E) ∈ S
    · simp [hS]
    simp only [hS, if_false]

    have h1 := (hmem _).1 (hc g h) w hS
    rw [← hval, hvdiv, hvmul] at h1
    have h2 : val (g • c h) w = val (c h) (g⁻¹ • w) := by
      have := hsm g (c h) (g⁻¹ • w)
      rwa [smul_inv_smul] at this
    rw [h2, div_eq_one_iff_eq (hvne _ _)] at h1
    rw [← h1, hlg_mul (hvne _ _) (hvne _ _)]

  obtain ⟨m, hm⟩ := groupCohomology.exists_forall_eq_sub_mapDomain_smul_of_forall_mul_eq_add_mapDomain_smul
    (fun g => nv (c g)) hcoc

  obtain ⟨q, hq⟩ := NumberField.AdeleRing.exists_units_forall_valued_snd_eq_ofAdd_neg K m
  refine ⟨q, fun g => (hmem _).2 fun w hS => ?_⟩
  rw [← hval, hvmul, hvinv, hvdiv]
  have hqw : val q w = ((Multiplicative.ofAdd (-(m w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hq w
  have hgqw : val (g • q) w = ((Multiplicative.ofAdd (-(m (g⁻¹ • w))) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    have := hsm g q (g⁻¹ • w)
    rw [smul_inv_smul] at this
    rw [hval, this]; exact hq _
  have hcw : val (c g) w = ((Multiplicative.ofAdd (m w - m (g⁻¹ • w)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    have hn : nv (c g) w = m w - m (g⁻¹ • w) := by rw [hm g, Finsupp.sub_apply, hmd]
    rw [hnv, if_neg (show w.under (𝓞 E) ∉ S from hS)] at hn
    rw [← hlg (hvne (c g) w), hn]
  rw [hqw, hgqw, hcw, ← WithZero.coe_div, ← WithZero.coe_inv, ← WithZero.coe_mul, ← ofAdd_sub, ← ofAdd_neg, ← ofAdd_add]
  convert WithZero.coe_one using 2
  simp only [ofAdd_eq_one]
  ring

end S_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_forall_mul_inv_smul_div_mem_unitIdelesOutside_of_forall_mem (solution)
