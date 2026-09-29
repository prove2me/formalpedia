-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/626130a1-d161-5bee-a699-ca45eceac4a8

import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_enorm_comp_iotaGL_mul_modulus_cpow_lt_top_of_gauge
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt
import Theorems.Thm_HaarQuotient_lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit'"
p2m_attr_erase "instance" "RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory NumberField.TateGlobal NumberField.AdelicLevel UnramifiedWhittaker AdelicDock LanglandsTunnell.TateLocal NumberField.StandardAddChar Topology

open scoped nonZeroDivisors NNReal ENNReal Matrix Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KcBigCellEngine

scoped instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

section Place

variable (p : HeightOneSpectrum (𝓞 ℚ))

def projAt : ↥(finiteAdelicGL2Subgroup ℚ) →* GL (Fin 2) (p.adicCompletion ℚ) :=
  (localAt ℚ p).comp (finiteAdelicGL2Subgroup ℚ).subtype

theorem projAt_apply (g : finiteAdelicGL2Subgroup ℚ) : projAt p g = localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) := rfl

theorem continuous_projAt : Continuous (projAt p) :=
  (continuous_localAt ℚ p).comp continuous_subtype_val

theorem localAt_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    (localAt ℚ p g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p := rfl

theorem localAt_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    localAt ℚ q (placeEmbed ℚ p x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ q (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ p x hq]

theorem localAt_unipotentGL2 (t : AdeleRing (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ v (unipotentGL2 t) = unipotentGL2 (t.2 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [localAt_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glArch_unipotentGL2 (t : AdeleRing (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (unipotentGL2 t) = unipotentGL2 t.1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_unipotentGL2_of_mem_adelicUnipotent {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) :
    ∃ t : AdeleRing (𝓞 ℚ) ℚ, n = unipotentGL2 t := by
  obtain ⟨a, rfl⟩ := hn
  exact ⟨a.toAdd, rfl⟩

theorem det_unipotentGL2 {A : Type*} [CommRing A] (x : A) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem unipotent_eq_unipotentGL2 {F : Type*} [Field F] (x : F) : unipotent x = unipotentGL2 x :=
  Units.ext rfl

theorem coe_finUnipotent_mem (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) :
    ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ := n.2

end Place

section LocalCell

variable (p : HeightOneSpectrum (𝓞 ℚ))

abbrev unipL : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) := (unipotentGL2Hom (R := p.adicCompletion ℚ)).range

abbrev kzero : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤

def locCell : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
  ((unipL p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) *
    ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))

theorem mem_locCell_iff (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    y ∈ locCell p ↔ ∃ n ∈ unipL p, ∃ k ∈ kzero p, y = n * k := by
  rw [locCell, Set.mem_mul]
  constructor
  · rintro ⟨n, hn, k, hk, h⟩; exact ⟨n, hn, k, hk, h.symm⟩
  · rintro ⟨n, hn, k, hk, h⟩; exact ⟨n, hn, k, hk, h.symm⟩

theorem mem_kzero_iff (k : GL (Fin 2) (p.adicCompletion ℚ)) :
    k ∈ kzero p ↔ (∀ i j, (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ) ∧
      ∀ i j, ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j ∈
        p.adicCompletionIntegers ℚ := by
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) →
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m h
    refine ⟨h, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
    · rw [AdelicLevel.idealBound_top]
      calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : p.adicCompletion ℚ)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩; exact ⟨aux _ h1, aux _ h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) = localIntegralSet ℚ p := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet ℚ p

theorem isCompact_kzero : IsCompact ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet ℚ p

theorem isOpen_locCell : IsOpen (locCell p) := (isOpen_kzero p).mul_left

theorem coe_unipL_eq :
    ((unipL p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) =
      {g : GL (Fin 2) (p.adicCompletion ℚ) | (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unipL : IsClosed ((unipL p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
  rw [coe_unipL_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j :=
    fun i j => (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unipL_comm (a b : ↥(unipL p)) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  show (a : GL (Fin 2) (p.adicCompletion ℚ)) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem unipotent_mul_mem_locCell_iff (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    unipotentGL2 x * y ∈ locCell p ↔ y ∈ locCell p := by
  have hx : (unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) ∈ unipL p := ⟨Multiplicative.ofAdd x, rfl⟩
  rw [mem_locCell_iff, mem_locCell_iff]
  constructor
  · rintro ⟨n, hn, k, hk, h⟩
    refine ⟨(unipotentGL2 x)⁻¹ * n, Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hn, k, hk, ?_⟩
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  · rintro ⟨n, hn, k, hk, h⟩
    refine ⟨unipotentGL2 x * n, Subgroup.mul_mem _ hx hn, k, hk, ?_⟩
    rw [h, mul_assoc]

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem coe_modulus_eq_norm (x : p.adicCompletion ℚ) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem continuous_modulus_det_ofReal : Continuous fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) := by
  have : (fun y : GL (Fin 2) (p.adicCompletion ℚ) => ((LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) =
      fun y : GL (Fin 2) (p.adicCompletion ℚ) => ((‖(y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ : ℝ) : ℂ) := by
    funext y
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

theorem norm_eq_one_iff (x : p.adicCompletion ℚ) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p).ne'

theorem v_entry_le_one {k : GL (Fin 2) (p.adicCompletion ℚ)} (hk : k ∈ kzero p) (i j : Fin 2) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (((mem_kzero_iff p k).mp hk).1 i j)

theorem v_det_le_one_of_integral {m : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)} (h : ∀ i j, Valued.v (m i j) ≤ 1) :
    Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : GL (Fin 2) (p.adicCompletion ℚ)} (hk : k ∈ kzero p) :
    Valued.v (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 1 := by
  have h1 : Valued.v (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det ≤ 1 := v_det_le_one_of_integral p (v_entry_le_one p hk)
  have h2 : Valued.v ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det ≤ 1 :=
    v_det_le_one_of_integral p (v_entry_le_one p (inv_mem hk))
  have hprod : Valued.v (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det *
      Valued.v ((k⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det := hprod.symm
    _ ≤ Valued.v (k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det * 1 := by gcongr
    _ = _ := mul_one _

theorem norm_det_eq_one_of_mem_kzero {k : GL (Fin 2) (p.adicCompletion ℚ)} (hk : k ∈ kzero p) :
    ‖(k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det‖ = 1 :=
  (norm_eq_one_iff p _).2 (v_det_eq_one p hk)

theorem modulus_det_eq_one_of_mem_locCell {y : GL (Fin 2) (p.adicCompletion ℚ)} (hy : y ∈ locCell p) :
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) = 1 := by
  obtain ⟨n, hn, k, hk, rfl⟩ := (mem_locCell_iff p y).1 hy
  obtain ⟨z, rfl⟩ := hn
  rw [coe_modulus_eq_norm, map_mul, show unipotentGL2Hom z = unipotentGL2 z.toAdd from rfl, det_unipotentGL2, one_mul,
    Matrix.GeneralLinearGroup.val_det_apply, norm_det_eq_one_of_mem_kzero p hk]
  simp

end LocalCell

section Kf

def Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ) :=
  (finiteIntegralGL2 (𝓞 ℚ) ℚ).comap ((glFin (𝓞 ℚ) ℚ).comp (finiteAdelicGL2Subgroup ℚ).subtype)

theorem mem_Kf_iff (k : finiteAdelicGL2Subgroup ℚ) : k ∈ Kf ↔ glFin (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
  Iff.rfl

theorem mem_Kf_of_forall (k : finiteAdelicGL2Subgroup ℚ) (hk : ∀ p : HeightOneSpectrum (𝓞 ℚ), localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero p) :
    k ∈ Kf := by
  rw [mem_Kf_iff, mem_finiteIntegralGL2_iff]
  refine ⟨fun i j v => ?_, fun i j v => ?_⟩
  · have h := ((mem_kzero_iff v _).1 (hk v)).1 i j
    rwa [localAt_apply] at h
  · have h := ((mem_kzero_iff v _).1 (hk v)).2 i j
    rw [← map_inv, localAt_apply] at h
    exact h

theorem localAt_mem_kzero_of_mem_Kf {k : finiteAdelicGL2Subgroup ℚ} (hk : k ∈ Kf) (p : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ p (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero p := by
  rw [mem_Kf_iff, mem_finiteIntegralGL2_iff] at hk
  rw [mem_kzero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [localAt_apply]; exact hk.1 i j p
  · rw [← map_inv, localAt_apply]; exact hk.2 i j p

theorem isOpen_Kf : IsOpen ((Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) :=
  (isOpen_finiteLevelZero (𝓞 ℚ) ℚ (N := ⊤) (by simp)).preimage ((continuous_glFin (𝓞 ℚ) ℚ).comp continuous_subtype_val)

theorem continuous_finEmbed : Continuous (finEmbed (𝓞 ℚ) ℚ) := by
  have hfm : Continuous (finMat (𝓞 ℚ) ℚ) :=
    continuous_matrix fun i j =>
      (continuous_const.prodMk (continuous_id.matrix_elem i j) :
        Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
          ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j, g i j) : AdeleRing (𝓞 ℚ) ℚ)))
  exact Units.continuous_iff.2 ⟨hfm.comp Units.continuous_val, hfm.comp Units.continuous_coe_inv⟩

theorem finEmbed_mem (x : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : finEmbed (𝓞 ℚ) ℚ x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).2 (glArch_finEmbed (𝓞 ℚ) ℚ _)

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 ℚ) ℚ}
    (h₁ : glArch (𝓞 ℚ) ℚ x = glArch (𝓞 ℚ) ℚ y) (h₂ : glFin (𝓞 ℚ) ℚ x = glFin (𝓞 ℚ) ℚ y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) h₁
  have h₂' := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem finEmbed_glFin_of_mem (g : finiteAdelicGL2Subgroup ℚ) :
    finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ)) = g := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [glArch_finEmbed, (mem_finiteAdelicGL2Subgroup_iff ℚ _).1 g.2]
  · rw [glFin_finEmbed]

theorem isCompact_Kf : IsCompact ((Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) := by
  let φ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) → ↥(finiteAdelicGL2Subgroup ℚ) := fun x => ⟨finEmbed (𝓞 ℚ) ℚ x, finEmbed_mem x⟩
  have hφ : Continuous φ := continuous_finEmbed.subtype_mk _
  have himage : ((Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) =
      φ '' ((finiteIntegralGL2 (𝓞 ℚ) ℚ : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ))) : Set _) := by
    ext k
    constructor
    · intro hk
      exact ⟨glFin (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ), hk, Subtype.ext (finEmbed_glFin_of_mem k)⟩
    · rintro ⟨x, hx, rfl⟩
      show glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ x) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ
      rwa [glFin_finEmbed]
  rw [himage]
  exact (isCompact_finiteLevelZero (𝓞 ℚ) ℚ ⊤).image hφ

theorem ideleNorm_det_eq_one_of_mem_Kf {k : finiteAdelicGL2Subgroup ℚ} (hk : k ∈ Kf) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := by
  have hk' : glFin (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := hk
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ) hk']
  refine Finset.prod_eq_one fun w _ => ?_
  have h1 : NumberField.AdelicVolume.archDetNorm w (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    show ‖((archComponent ℚ w (glArch (𝓞 ℚ) ℚ (k : AdelicGL2 (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) w.Completion)).det‖ = 1
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).1 k.2, map_one, Units.val_one, Matrix.det_one, norm_one]
  rw [h1, one_pow]

theorem isClosed_finUnipotent :
    IsClosed ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : finiteAdelicGL2Subgroup ℚ =>
      ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).comp continuous_subtype_val
  have heq : ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) =
      {g : finiteAdelicGL2Subgroup ℚ | ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 0 = 1 ∧
        ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0 = 0 ∧
        ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1 = 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    show (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ ↔ _
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      simp [unipotentGL2Hom, unipotentGL2_coe]
    · rintro ⟨h00, h10, h11⟩
      refine ⟨Multiplicative.ofAdd (((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1), Units.ext ?_⟩
      change ((unipotentGL2 (((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 0 1) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
      rw [unipotentGL2_coe]
      ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  rw [heq]
  exact (isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1)))

theorem finUnipotent_comm (a b : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) : a * b = b * a := by
  obtain ⟨x, hx⟩ := coe_finUnipotent_mem a
  obtain ⟨y, hy⟩ := coe_finUnipotent_mem b
  refine Subtype.ext (Subtype.ext ?_)
  show ((a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * ((b : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
    ((b : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * ((a : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ' : Measure G) [μ'.IsMulLeftInvariant] (hcomm : ∀ a b : G, a * b = b * a) : μ'.IsMulRightInvariant := by
  constructor
  intro g
  have : (fun h : G => h * g) = fun h => g * h := funext fun h => hcomm h g
  rw [this]
  exact MeasureTheory.map_mul_left_eq_self μ' g

theorem mem_finUnipotent_mul_Kf (g : finiteAdelicGL2Subgroup ℚ)
    (hg : ∀ p : HeightOneSpectrum (𝓞 ℚ), localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell p) :
    g ∈ ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) *
      ((Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) := by
  classical
  choose n hn k hk hnk using fun p => (mem_locCell_iff p _).1 (hg p)
  choose z hz using hn

  let t : (p : HeightOneSpectrum (𝓞 ℚ)) → p.adicCompletion ℚ := fun p =>
    if localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero p then 0 else (z p).toAdd
  have hfin : {p : HeightOneSpectrum (𝓞 ℚ) | localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) ∉ kzero p}.Finite := by
    have hent : ∀ (Z : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2),
        {v : HeightOneSpectrum (𝓞 ℚ) | ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v ∉ v.adicCompletionIntegers ℚ}.Finite :=
      fun Z i j => Filter.eventually_cofinite.1 ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
    refine (((Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent (g : AdelicGL2 (𝓞 ℚ) ℚ) i j)).union
      (Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent (g : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ i j)).subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, mem_kzero_iff, not_and_or, not_forall] at hv
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
    rcases hv with ⟨i, j, h⟩ | ⟨i, j, h⟩
    · exact Or.inl ⟨i, j, h⟩
    · refine Or.inr ⟨i, j, ?_⟩
      rwa [← map_inv] at h
  have ht : ∀ᶠ p in Filter.cofinite, t p ∈ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    refine Filter.eventually_cofinite.2 (hfin.subset fun p hp => ?_)
    intro hmem
    apply hp
    simp only [t, if_pos hmem, SetLike.mem_coe, zero_mem]
  let tf : FiniteAdeleRing (𝓞 ℚ) ℚ := ⟨t, ht⟩
  let ta : AdeleRing (𝓞 ℚ) ℚ := (0, tf)
  have hnmem : unipotentGL2 ta ∈ finiteAdelicGL2Subgroup ℚ := by
    rw [mem_finiteAdelicGL2Subgroup_iff, glArch_unipotentGL2]
    exact unipotentGL2_zero
  let N : finiteAdelicGL2Subgroup ℚ := ⟨unipotentGL2 ta, hnmem⟩
  have hNu : N ∈ RSCarrier.finUnipotent := by
    show (unipotentGL2 ta : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ
    exact ⟨Multiplicative.ofAdd ta, rfl⟩
  have hloc : ∀ p, localAt ℚ p (N : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (t p) := fun p => localAt_unipotentGL2 ta p
  refine Set.mem_mul.2 ⟨N, hNu, N⁻¹ * g, ?_, mul_inv_cancel_left N g⟩
  refine mem_Kf_of_forall _ fun p => ?_
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hloc p]
  by_cases hmem : localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero p
  · simp only [t, if_pos hmem, unipotentGL2_zero, inv_one, one_mul]
    exact hmem
  · simp only [t, if_neg hmem]
    have hng : localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (z p).toAdd * k p := by
      rw [hnk p, ← hz p]; rfl
    rw [hng, inv_mul_cancel_left]
    exact hk p

end Kf

theorem continuous_iotaGL {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] :
    Continuous (iotaGL : GL (Fin 2) F →* GL (Fin 3) F) := by
  have hE : Continuous (embedMat2 : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 3) (Fin 3) F) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals first
      | exact continuous_const
      | exact continuous_id.matrix_elem _ _
  refine Units.continuous_iff.2 ⟨hE.comp Units.continuous_val, ?_⟩
  have h : ∀ g : GL (Fin 2) F, ((((iotaGL g : GL (Fin 3) F)⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      embedMat2 ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := fun g => by rw [← map_inv, coe_iotaGL]
  simp_rw [h]
  exact hE.comp Units.continuous_coe_inv

section EulerFamily

variable (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)

open scoped Classical in

def eFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  if v ∈ S' then 1 else L v (iotaGL (localAt ℚ v Y))

def Efun (Y : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ := ∏ᶠ v, eFam S' L Y v

def fFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ := L v (iotaGL (localAt ℚ v Y))

variable {S' L}

theorem eFam_of_mem (Y : AdelicGL2 (𝓞 ℚ) ℚ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ S') : eFam S' L Y v = 1 := by
  simp [eFam, hv]

theorem eFam_of_not_mem (Y : AdelicGL2 (𝓞 ℚ) ℚ) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S') :
    eFam S' L Y v = L v (iotaGL (localAt ℚ v Y)) := by
  simp [eFam, hv]

theorem finite_setOf_not_mem_kzero (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | localAt ℚ v Y ∉ kzero v}.Finite := by
  have hent : ∀ (Z : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2),
      {v : HeightOneSpectrum (𝓞 ℚ) | ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    fun Z i j => Filter.eventually_cofinite.1 ((Z : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
  refine (((Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y i j)).union
    (Set.finite_iUnion fun i => Set.finite_iUnion fun j => hent Y⁻¹ i j)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, mem_kzero_iff, not_and_or, not_forall] at hv
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq]
  rcases hv with ⟨i, j, h⟩ | ⟨i, j, h⟩
  · exact Or.inl ⟨i, j, h⟩
  · refine Or.inr ⟨i, j, ?_⟩
    rwa [← map_inv] at h

variable (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
include hLone

theorem mulSupport_fFam_subset (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    Function.mulSupport (fFam L Y) ⊆ (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ∪ {v | localAt ℚ v Y ∉ kzero v} := by
  intro v hv
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv (hLone v h.1 _ h.2)

theorem finite_mulSupport_fFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) : (Function.mulSupport (fFam L Y)).Finite :=
  ((S'.finite_toSet).union (finite_setOf_not_mem_kzero Y)).subset (mulSupport_fFam_subset hLone Y)

theorem mulSupport_eFam_subset (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    Function.mulSupport (eFam S' L Y) ⊆ {v | localAt ℚ v Y ∉ kzero v} := by
  intro v hv
  by_contra h
  simp only [Set.mem_setOf_eq, not_not] at h
  apply hv
  by_cases hvS : v ∈ S'
  · exact eFam_of_mem Y hvS
  · rw [eFam_of_not_mem Y hvS]; exact hLone v hvS _ h

theorem finite_mulSupport_eFam (Y : AdelicGL2 (𝓞 ℚ) ℚ) : (Function.mulSupport (eFam S' L Y)).Finite :=
  (finite_setOf_not_mem_kzero Y).subset (mulSupport_eFam_subset hLone Y)

theorem finprod_fFam_eq (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∏ᶠ v, L v (iotaGL (localAt ℚ v Y)) = (∏ v ∈ S', L v (iotaGL (localAt ℚ v Y))) * Efun S' L Y := by
  classical
  have hfin := finite_mulSupport_fFam hLone Y
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := S' ∪ hfin.toFinset with hT
  have h1 : Function.mulSupport (fFam L Y) ⊆ (T : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v hv; simp [hT, hv]
  have h2 : Function.mulSupport (eFam S' L Y) ⊆ (T : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v hv
    by_cases hvS : v ∈ S'
    · simp [hT, hvS]
    · rw [Function.mem_mulSupport, eFam_of_not_mem Y hvS] at hv
      have : v ∈ Function.mulSupport (fFam L Y) := hv
      simp [hT, this]
  change ∏ᶠ v, fFam L Y v = (∏ v ∈ S', fFam L Y v) * Efun S' L Y
  rw [Efun, finprod_eq_prod_of_mulSupport_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2,
    ← Finset.prod_sdiff (Finset.subset_union_left : S' ⊆ T)]
  have h3 : ∏ v ∈ T \ S', fFam L Y v = ∏ v ∈ T \ S', eFam S' L Y v :=
    Finset.prod_congr rfl fun v hv => by rw [eFam_of_not_mem Y (Finset.mem_sdiff.1 hv).2]; rfl
  have h4 : ∏ v ∈ S', eFam S' L Y v = 1 := Finset.prod_eq_one fun v hv => eFam_of_mem Y hv
  rw [h3, mul_comm, ← Finset.prod_sdiff (Finset.subset_union_left : S' ⊆ T), h4, mul_one]

omit hLone in

theorem eFam_mul_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S')
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : eFam S' L (Y * placeEmbed ℚ p x) = eFam S' L Y := by
  funext v
  by_cases hv : v ∈ S'
  · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
  · have hne : v ≠ p := fun h => hv (h ▸ hp)
    rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv, map_mul, localAt_placeEmbed_of_ne p hne, mul_one]

omit hLone in
theorem Efun_mul_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S')
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : Efun S' L (Y * placeEmbed ℚ p x) = Efun S' L Y := by
  simp only [Efun, eFam_mul_placeEmbed Y hp x]

variable (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
include hLphase

theorem norm_Efun_unipotentGL2_mul (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    ‖Efun S' L (unipotentGL2 t * Y)‖ = ‖Efun S' L Y‖ := by
  classical
  have hn : ∀ v, ‖eFam S' L (unipotentGL2 t * Y) v‖ = ‖eFam S' L Y v‖ := by
    intro v
    by_cases hv : v ∈ S'
    · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
    · rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv, map_mul, localAt_unipotentGL2, map_mul, hLphase]
  have hf1 := finite_mulSupport_eFam hLone (unipotentGL2 t * Y)
  have hf2 := finite_mulSupport_eFam hLone Y
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := hf1.toFinset ∪ hf2.toFinset with hT
  have h1 : Function.mulSupport (eFam S' L (unipotentGL2 t * Y)) ⊆ (T : Set _) := by intro v hv; simp [hT, hv]
  have h2 : Function.mulSupport (eFam S' L Y) ⊆ (T : Set _) := by intro v hv; simp [hT, hv]
  simp only [Efun]
  rw [finprod_eq_prod_of_mulSupport_subset _ h1, finprod_eq_prod_of_mulSupport_subset _ h2, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun v _ => hn v

theorem norm_Efun_eq_one_of_forall (Y : AdelicGL2 (𝓞 ℚ) ℚ)
    (hY : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v Y ∈ locCell v) : ‖Efun S' L Y‖ = 1 := by
  classical
  have hn : ∀ v, ‖eFam S' L Y v‖ = 1 := by
    intro v
    by_cases hv : v ∈ S'
    · rw [eFam_of_mem _ hv, norm_one]
    · rw [eFam_of_not_mem _ hv]
      obtain ⟨n, hn, k, hk, h⟩ := (mem_locCell_iff v _).1 (hY v hv)
      obtain ⟨z, rfl⟩ := hn
      rw [h, map_mul, show unipotentGL2Hom z = unipotentGL2 z.toAdd from rfl, hLphase, hLone v hv k hk, norm_one]
  have hf := finite_mulSupport_eFam hLone Y
  simp only [Efun]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hf.toFinset) (by simp), norm_prod]
  exact Finset.prod_eq_one fun v _ => hn v

omit hLphase

variable (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
include hLlc

omit hLone in

theorem continuous_fFam_coe (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) :=
  (hLlc v).continuous.comp ((continuous_iotaGL).comp (continuous_projAt v))

theorem continuous_Efun_coe : Continuous fun g : finiteAdelicGL2Subgroup ℚ => Efun S' L (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  classical
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun g₀ => ?_)

  have hfin := finite_setOf_not_mem_kzero (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)
  set T : Finset (HeightOneSpectrum (𝓞 ℚ)) := S' ∪ hfin.toFinset with hT
  let κ : finiteAdelicGL2Subgroup ℚ → AdelicGL2 (𝓞 ℚ) ℚ := fun g => (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹ * g
  have hκ : Continuous κ := continuous_const.mul continuous_subtype_val

  let N : Set (finiteAdelicGL2Subgroup ℚ) :=
    {g | ∀ v, localAt ℚ v (κ g) ∈ kzero v} ∩
      ⋂ v ∈ T, {g | L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) = L v (iotaGL (localAt ℚ v (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)))}
  have hopen1 : IsOpen {g : finiteAdelicGL2Subgroup ℚ | ∀ v, localAt ℚ v (κ g) ∈ kzero v} := by
    have hO : IsOpen {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} := by
      have hc : ∀ i j : Fin 2, Continuous fun Y : AdelicGL2 (𝓞 ℚ) ℚ => ((Y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 :=
        fun i j => continuous_snd.comp (Units.continuous_val.matrix_elem i j)
      have hc' : ∀ i j : Fin 2, Continuous fun Y : AdelicGL2 (𝓞 ℚ) ℚ =>
          (((Y⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 :=
        fun i j => continuous_snd.comp (Units.continuous_coe_inv.matrix_elem i j)
      have heq : {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} =
          (⋂ i, ⋂ j, (fun Y : AdelicGL2 (𝓞 ℚ) ℚ => ((Y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) ⁻¹'
            {y | ∀ v : HeightOneSpectrum (𝓞 ℚ), y v ∈ v.adicCompletionIntegers ℚ}) ∩
          ⋂ i, ⋂ j, (fun Y : AdelicGL2 (𝓞 ℚ) ℚ => (((Y⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) ⁻¹'
            {y | ∀ v : HeightOneSpectrum (𝓞 ℚ), y v ∈ v.adicCompletionIntegers ℚ} := by
        ext Y
        simp only [Set.mem_setOf_eq, mem_localIntegralSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
        constructor
        · intro h; exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
        · intro h v; exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩
      rw [heq]
      exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_forall_mem_integers.preimage (hc i j)).inter
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_forall_mem_integers.preimage (hc' i j))
    have heq' : {g : finiteAdelicGL2Subgroup ℚ | ∀ v, localAt ℚ v (κ g) ∈ kzero v} =
        κ ⁻¹' {Y : AdelicGL2 (𝓞 ℚ) ℚ | ∀ v, localAt ℚ v Y ∈ localIntegralSet ℚ v} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      refine forall_congr' fun v => ?_
      rw [← SetLike.mem_coe, coe_kzero_eq_localIntegralSet]
    rw [heq']
    exact hO.preimage hκ
  have hopen2 : ∀ v ∈ T, IsOpen {g : finiteAdelicGL2Subgroup ℚ |
      L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) = L v (iotaGL (localAt ℚ v (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)))} :=
    fun v _ => ((hLlc v).isOpen_fiber _).preimage ((continuous_iotaGL).comp (continuous_projAt v))
  have hN : IsOpen N := hopen1.inter (isOpen_biInter_finset hopen2)
  have hg₀ : g₀ ∈ N := by
    refine ⟨fun v => ?_, ?_⟩
    · simp only [κ, inv_mul_cancel, map_one]; exact (kzero v).one_mem
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro v _; trivial
  refine ⟨N, hN, hg₀, fun g hg => ?_⟩
  have hgκ : (g : AdelicGL2 (𝓞 ℚ) ℚ) = (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) * κ g := by simp only [κ, mul_inv_cancel_left]
  simp only [Efun]
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ S'
  · rw [eFam_of_mem _ hv, eFam_of_mem _ hv]
  rw [eFam_of_not_mem _ hv, eFam_of_not_mem _ hv]
  by_cases hvT : v ∈ T
  · have := hg.2
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at this
    exact this v hvT
  ·
    have h0 : localAt ℚ v (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero v := by
      by_contra h
      apply hvT
      rw [hT]
      exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)
    have h1 : localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ kzero v := by
      rw [hgκ, map_mul]
      exact (kzero v).mul_mem h0 (hg.1 v)
    rw [hLone v hv _ h1, hLone v hv _ h0]

theorem continuous_finprod_fFam_coe :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v, L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ))) := by
  have : (fun g : finiteAdelicGL2Subgroup ℚ => ∏ᶠ v, L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) =
      fun g : finiteAdelicGL2Subgroup ℚ =>
        (∏ v ∈ S', L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * Efun S' L (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
    funext fun g => finprod_fFam_eq hLone _
  rw [this]
  exact (continuous_finsetProd _ fun v _ => continuous_fFam_coe hLlc v).mul (continuous_Efun_coe hLone hLlc)

end EulerFamily

section Cells

variable (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ)))

def bigCell : Set ↥(finiteAdelicGL2Subgroup ℚ) :=
  {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
    ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

theorem mem_bigCell_iff (g : finiteAdelicGL2Subgroup ℚ) :
    g ∈ bigCell SQ ↔ ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell p := by
  refine forall_congr' fun p => forall_congr' fun _ => ?_
  rw [mem_locCell_iff]

theorem measurableSet_bigCell : MeasurableSet (bigCell SQ) := by
  have heq : bigCell SQ = ⋂ p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, (projAt p.1) ⁻¹' locCell p.1 := by
    ext g
    rw [mem_bigCell_iff]
    simp only [Set.mem_iInter, Set.mem_preimage, Subtype.forall, projAt_apply]
  rw [heq]
  exact MeasurableSet.iInter fun p => ((isOpen_locCell p.1).preimage (continuous_projAt p.1)).measurableSet

open scoped Classical in

def cellAway (Y : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v Y ∈ locCell v then 1 else 0

open scoped Classical in

def cfac (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  if p ∈ SQ then 1 else if y ∈ locCell p then 1 else 0

open scoped Classical in

def refFac (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ :=
  if y ∈ locCell p then 1 else 0

variable {SQ S'}

theorem cellAway_mul_placeEmbed (Y : AdelicGL2 (𝓞 ℚ) ℚ) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S')
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : cellAway S' (Y * placeEmbed ℚ p x) = cellAway S' Y := by
  classical
  have : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (Y * placeEmbed ℚ p x) ∈ locCell v) ↔
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v Y ∈ locCell v := by
    refine forall_congr' fun v => forall_congr' fun hv => ?_
    have hne : v ≠ p := fun h => hv (h ▸ hp)
    rw [map_mul, localAt_placeEmbed_of_ne p hne, mul_one]
  simp only [cellAway, this]

theorem cellAway_unipotentGL2_mul (t : AdeleRing (𝓞 ℚ) ℚ) (Y : AdelicGL2 (𝓞 ℚ) ℚ) :
    cellAway S' (unipotentGL2 t * Y) = cellAway S' Y := by
  classical
  have : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (unipotentGL2 t * Y) ∈ locCell v) ↔
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v Y ∈ locCell v := by
    refine forall_congr' fun v => forall_congr' fun _ => ?_
    rw [map_mul, localAt_unipotentGL2, unipotent_mul_mem_locCell_iff]
  simp only [cellAway, this]

theorem norm_cellAway_le_one (Y : AdelicGL2 (𝓞 ℚ) ℚ) : ‖cellAway S' Y‖ ≤ 1 := by
  classical
  unfold cellAway; split_ifs <;> simp

theorem cfac_unipotent_mul (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    cfac SQ p (unipotent x * y) = cfac SQ p y := by
  classical
  simp only [cfac, unipotent_eq_unipotentGL2, unipotent_mul_mem_locCell_iff]

theorem refFac_unipotent_mul (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    refFac p (unipotent x * y) = refFac p y := by
  classical
  simp only [refFac, unipotent_eq_unipotentGL2, unipotent_mul_mem_locCell_iff]

theorem norm_cfac_le_one (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)) : ‖cfac SQ p y‖ ≤ 1 := by
  classical
  unfold cfac; split_ifs <;> simp

theorem cfac_eq_one_of_mem_locCell (p : HeightOneSpectrum (𝓞 ℚ)) {y : GL (Fin 2) (p.adicCompletion ℚ)} (hy : y ∈ locCell p) :
    cfac SQ p y = 1 := by
  classical
  unfold cfac; split_ifs <;> rfl

theorem refFac_eq_indicator (p : HeightOneSpectrum (𝓞 ℚ)) : refFac p = (locCell p).indicator fun _ => (1 : ℂ) := by
  classical
  funext y; simp [refFac, Set.indicator_apply]

theorem measurable_cfac (p : HeightOneSpectrum (𝓞 ℚ)) : Measurable[localGLBorel ℚ p] (cfac SQ p) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  by_cases hp : p ∈ SQ
  · have : cfac SQ p = fun _ => 1 := funext fun y => by simp [cfac, hp]
    rw [this]; exact measurable_const
  · have : cfac SQ p = (locCell p).indicator fun _ => (1 : ℂ) := funext fun y => by simp [cfac, hp, Set.indicator_apply]
    rw [this]; exact measurable_const.indicator (isOpen_locCell p).measurableSet

theorem measurable_refFac (p : HeightOneSpectrum (𝓞 ℚ)) : Measurable[localGLBorel ℚ p] (refFac p) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  rw [refFac_eq_indicator]
  exact measurable_const.indicator (isOpen_locCell p).measurableSet

theorem measurable_cellAway_coe : Measurable fun g : finiteAdelicGL2Subgroup ℚ => cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
  classical
  have hset : MeasurableSet {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' →
      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell v} := by
    have heq : {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell v} =
        ⋂ p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S'}, (projAt p.1) ⁻¹' locCell p.1 := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Subtype.forall, projAt_apply]
    rw [heq]
    exact MeasurableSet.iInter fun p => ((isOpen_locCell p.1).preimage (continuous_projAt p.1)).measurableSet
  have : (fun g : finiteAdelicGL2Subgroup ℚ => cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
      {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell v}.indicator
        fun _ => (1 : ℂ) := by
    funext g; simp [cellAway, Set.indicator_apply]
  rw [this]
  exact measurable_const.indicator hset

theorem indicator_bigCell_eq (hSS' : SQ ⊆ S') (f : finiteAdelicGL2Subgroup ℚ → ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    (bigCell SQ).indicator f g =
      (∏ p ∈ S', cfac SQ p (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) * cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) * f g := by
  classical
  by_cases hg : g ∈ bigCell SQ
  · rw [Set.indicator_of_mem hg]
    rw [mem_bigCell_iff] at hg
    have h1 : ∏ p ∈ S', cfac SQ p (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := by
      refine Finset.prod_eq_one fun p _ => ?_
      by_cases hp : p ∈ SQ
      · simp [cfac, hp]
      · exact cfac_eq_one_of_mem_locCell p (hg p hp)
    have h2 : cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
      simp only [cellAway]
      rw [if_pos fun v hv => hg v fun h => hv (hSS' h)]
    rw [h1, h2, one_mul, one_mul]
  · rw [Set.indicator_of_notMem hg]
    rw [mem_bigCell_iff] at hg
    push Not at hg
    obtain ⟨p, hp, hnot⟩ := hg
    by_cases hpS : p ∈ S'
    · have h1 : ∏ q ∈ S', cfac SQ q (localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 0 := by
        refine Finset.prod_eq_zero hpS ?_
        simp [cfac, hp, hnot]
      rw [h1, zero_mul, zero_mul]
    · have h2 : cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) = 0 := by
        simp only [cellAway]
        rw [if_neg]
        intro h
        exact hnot (h p hpS)
      rw [h2, mul_zero, zero_mul]

end Cells

section Frozen

variable (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (M : ℝ)

theorem continuous_det_adelic : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det),
    (Units.continuous_coe_inv.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det)⟩

theorem continuous_ideleNorm_det_coe :
    Continuous fun g : finiteAdelicGL2Subgroup ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
  ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_adelic).comp continuous_subtype_val

def cw (s : ℂ) (g : finiteAdelicGL2Subgroup ℚ) : ℂ :=
  ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2)

theorem measurable_cw (s : ℂ) : Measurable (cw s) :=
  (Complex.continuous_ofReal.comp continuous_ideleNorm_det_coe).measurable.pow_const _

theorem norm_cw (s : ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    ‖cw s g‖ = ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ (s.re - 1 / 2) := by
  rw [cw, Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos _)]
  congr 1
  simp [Complex.sub_re]

def aFac (p : HeightOneSpectrum (𝓞 ℚ)) (y : GL (Fin 2) (p.adicCompletion ℚ)) : ℂ := cfac SQ p y * L p (iotaGL y)

def Vfun (X : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ := (M : ℂ) * (cellAway S' X * Efun S' L X)

open scoped Classical in

def frozen (T : Finset ↥S') (X : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  (∏ p ∈ T, aFac SQ L p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X)) *
    (∏ p ∈ Finset.univ \ T, refFac p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X)) * Vfun S' L M X

variable {SQ S' L M}

variable (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
  (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
  (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))

include hLphase in
theorem aFac_unipotent_mul (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) (y : GL (Fin 2) (p.adicCompletion ℚ)) :
    ‖aFac SQ L p (unipotent x * y)‖ = ‖aFac SQ L p y‖ := by
  rw [aFac, aFac, norm_mul, norm_mul, cfac_unipotent_mul, unipotent_eq_unipotentGL2, map_mul, hLphase]

include hLlc in
theorem measurable_aFac (p : HeightOneSpectrum (𝓞 ℚ)) : Measurable[localGLBorel ℚ p] (aFac SQ L p) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  exact (measurable_cfac p).mul ((hLlc p).continuous.comp continuous_iotaGL).measurable

theorem Vfun_mul_placeEmbed {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S') (x : GL (Fin 2) (p.adicCompletion ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ) :
    Vfun S' L M (X * placeEmbed ℚ p x) = Vfun S' L M X := by
  simp only [Vfun, cellAway_mul_placeEmbed X hp x, Efun_mul_placeEmbed X hp x]

include hLone hLphase in
theorem norm_Vfun_unipotent_mul (n : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) (g : finiteAdelicGL2Subgroup ℚ) :
    ‖Vfun S' L M ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
      ‖Vfun S' L M (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ := by
  obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem n)
  rw [Subgroup.coe_mul, ht]
  simp only [Vfun, norm_mul, cellAway_unipotentGL2_mul, norm_Efun_unipotentGL2_mul hLone hLphase]

include hLone hLlc in
theorem measurable_Vfun_coe : Measurable fun g : finiteAdelicGL2Subgroup ℚ => Vfun S' L M (g : AdelicGL2 (𝓞 ℚ) ℚ) :=
  measurable_const.mul (measurable_cellAway_coe.mul (continuous_Efun_coe hLone hLlc).measurable)

end Frozen

section LocalInputs

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem lintegral_locCell_ne_zero_and_lt_top :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipL p)) [μN₂.IsHaarMeasure],
    (∫⁻ y, (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂))) ≠ 0 ∧
    (∫⁻ y, (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂))) < ⊤ := by
  intro μ₂ _ μN₂ _
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI := secondCountableTopology_localGL p
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_of_comm μN₂ (unipL_comm p)
  obtain ⟨heq, hlt⟩ := HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top μ₂ (unipL p)
    (isClosed_unipL p) μN₂ (kzero p) (isOpen_kzero p) (isCompact_kzero p)
  refine ⟨?_, hlt⟩
  change (∫⁻ y, (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂))) =
    μ₂ (kzero p) / μN₂ (((↑) : ↥(unipL p) → GL (Fin 2) (p.adicCompletion ℚ)) ⁻¹' (kzero p : Set (GL (Fin 2) (p.adicCompletion ℚ)))) at heq
  rw [heq]
  refine (ENNReal.div_pos_iff.2 ⟨?_, ?_⟩).ne'
  · exact (isOpen_kzero p).measure_ne_zero μ₂ ⟨1, (kzero p).one_mem⟩
  · exact ((isClosed_unipL p).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_kzero p)).measure_lt_top.ne

variable {p}

theorem lintegral_locCell_mul_lt_top (L : LocalGL3 p → ℂ) (hLlc : IsLocallyConstant L)
    (hLphase : ∀ (x : p.adicCompletion ℚ) (h : LocalGL3 p), ‖L (iotaGL (unipotentGL2 x) * h)‖ = ‖L h‖) (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipL p)) [μN₂.IsHaarMeasure],
    (∫⁻ y, ‖(refFac p y * L (iotaGL y) * 1) *
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
          (s - 1 / 2)‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂))) < ⊤ := by
  intro μ₂ _ μN₂ _
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p

  obtain ⟨Msup, hMsup⟩ := (isCompact_kzero p).exists_bound_of_continuousOn
    ((hLlc.continuous.comp continuous_iotaGL).continuousOn : ContinuousOn (fun k : GL (Fin 2) (p.adicCompletion ℚ) => L (iotaGL k)) _)
  have hM0 : 0 ≤ Msup := (norm_nonneg _).trans (hMsup 1 (kzero p).one_mem)
  have hpt : ∀ y, ‖(refFac p y * L (iotaGL y) * 1) *
      ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
        (s - 1 / 2)‖ₑ ≤ ENNReal.ofReal Msup * (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    classical
    by_cases hy : y ∈ locCell p
    · rw [Set.indicator_of_mem hy, mul_one, refFac, if_pos hy, one_mul, mul_one, modulus_det_eq_one_of_mem_locCell p hy,
        Complex.one_cpow, mul_one, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      obtain ⟨n, hn, k, hk, rfl⟩ := (mem_locCell_iff p y).1 hy
      obtain ⟨z, rfl⟩ := hn
      rw [map_mul, show unipotentGL2Hom z = unipotentGL2 z.toAdd from rfl, hLphase]
      exact hMsup k hk
    · rw [refFac, if_neg hy, zero_mul, zero_mul, zero_mul, enorm_zero]
      exact bot_le
  have hmeas : Measurable ((locCell p).indicator fun _ => (1 : ℝ≥0∞)) := measurable_const.indicator (isOpen_locCell p).measurableSet
  calc _ ≤ ∫⁻ y, ENNReal.ofReal Msup * (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal Msup * ∫⁻ y, (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂)) :=
        lintegral_const_mul _ hmeas
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_locCell_ne_zero_and_lt_top p μ₂ μN₂).2

theorem lintegral_refFac_ne_zero (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipL p)) [μN₂.IsHaarMeasure],
    (∫⁻ y, ‖(refFac p y * 1) *
        ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
          (s - 1 / 2)‖ₑ ∂(μ₂.withDensity (HaarQuotient.density (unipL p) μN₂))) ≠ 0 := by
  intro μ₂ _ μN₂ _
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  have hpt : ∀ y, ‖(refFac p y * 1) *
      ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
        (s - 1 / 2)‖ₑ = (locCell p).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    classical
    by_cases hy : y ∈ locCell p
    · rw [Set.indicator_of_mem hy, refFac, if_pos hy, one_mul, modulus_det_eq_one_of_mem_locCell p hy, Complex.one_cpow,
        one_mul, enorm_one]
    · rw [Set.indicator_of_notMem hy, refFac, if_neg hy, zero_mul, zero_mul, enorm_zero]
  rw [lintegral_congr hpt]
  exact (lintegral_locCell_ne_zero_and_lt_top p μ₂ μN₂).1

end LocalInputs

section Base

variable {SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))} {L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ} {M : ℝ}
  (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
  (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
  (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
include hLone hLphase hLlc

theorem integrable_base [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] (σ₀ : ℝ) :
    Integrable (fun g : finiteAdelicGL2Subgroup ℚ => frozen SQ S' L M ∅ (g : AdelicGL2 (𝓞 ℚ) ℚ) * cw (σ₀ : ℂ) g)
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical
  haveI : LocallyCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : μNFin.IsMulRightInvariant := isMulRightInvariant_of_comm μNFin finUnipotent_comm
  haveI : SecondCountableTopology ↥(finiteAdelicGL2Subgroup ℚ) := TopologicalSpace.Subtype.secondCountableTopology _
  set ν := μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin) with hν
  set NK : Set ↥(finiteAdelicGL2Subgroup ℚ) := ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set _) *
    ((Kf : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set _) with hNK
  have hNKo : IsOpen NK := isOpen_Kf.mul_left
  obtain ⟨-, hlt⟩ := HaarQuotient.lintegral_indicator_coe_mul_coe_withDensity_density_eq_div_and_lt_top μf
    (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) isClosed_finUnipotent μNFin Kf isOpen_Kf isCompact_Kf
  have hνNK : ν NK < ⊤ := by
    rw [hν, ← lintegral_indicator_one hNKo.measurableSet]
    exact hlt

  have hdom : Integrable (NK.indicator fun _ => (|M| : ℝ)) ν :=
    (integrable_indicator_iff hNKo.measurableSet).2 (integrableOn_const hνNK.ne)

  have hmeas : Measurable fun g : finiteAdelicGL2Subgroup ℚ => frozen SQ S' L M ∅ (g : AdelicGL2 (𝓞 ℚ) ℚ) * cw (σ₀ : ℂ) g := by
    have h1 : ∀ q : ↥S', Measurable fun g : finiteAdelicGL2Subgroup ℚ => refFac (q : HeightOneSpectrum (𝓞 ℚ))
        (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) := fun q => by
      letI : MeasurableSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      haveI : BorelSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      exact (measurable_refFac (q : HeightOneSpectrum (𝓞 ℚ))).comp (continuous_projAt (q : HeightOneSpectrum (𝓞 ℚ))).measurable
    simp only [frozen, Finset.prod_empty, one_mul, Finset.sdiff_empty]
    exact ((Finset.measurable_prod _ fun q _ => h1 q).mul (measurable_Vfun_coe hLone hLlc)).mul (measurable_cw _)
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)

  by_cases hall : (∀ q : ↥S', localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell (q : HeightOneSpectrum (𝓞 ℚ))) ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell v
  ·
    have hg : ∀ v : HeightOneSpectrum (𝓞 ℚ), localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ locCell v := by
      intro v
      by_cases hv : v ∈ S'
      · exact hall.1 ⟨v, hv⟩
      · exact hall.2 v hv
    have hmem : g ∈ NK := mem_finUnipotent_mul_Kf g hg
    rw [Set.indicator_of_mem hmem]

    have h1 : ‖∏ q ∈ (Finset.univ : Finset ↥S') \ ∅, refFac (q : HeightOneSpectrum (𝓞 ℚ))
        (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun q _ => ?_
      rw [refFac, if_pos (hg _), norm_one]
    have h2 : ‖cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ = 1 := by
      simp only [cellAway]; rw [if_pos hall.2, norm_one]
    have h3 : ‖Efun S' L (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ = 1 := norm_Efun_eq_one_of_forall hLone hLphase _ hall.2
    have h4 : ‖cw (σ₀ : ℂ) g‖ = 1 := by
      obtain ⟨n, hn, k, hk, hgnk⟩ := Set.mem_mul.1 hmem
      obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (show ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ from hn)
      rw [norm_cw, ← hgnk, Subgroup.coe_mul, map_mul, ideleNorm_mul, ht, det_unipotentGL2, ideleNorm_det_eq_one_of_mem_Kf hk]
      simp [ideleNorm]
    rw [norm_mul, frozen, Finset.prod_empty, one_mul, norm_mul, h1, one_mul, Vfun, norm_mul, norm_mul, h2, h3, h4,
      Complex.norm_real, Real.norm_eq_abs]
    simp
  ·
    have hzero : frozen SQ S' L M ∅ (g : AdelicGL2 (𝓞 ℚ) ℚ) = 0 := by
      rw [not_and_or] at hall
      rcases hall with h | h
      · push Not at h
        obtain ⟨q, hq⟩ := h
        have : ∏ q ∈ (Finset.univ : Finset ↥S') \ ∅, refFac (q : HeightOneSpectrum (𝓞 ℚ))
            (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 0 := by
          refine Finset.prod_eq_zero (by simp : q ∈ (Finset.univ : Finset ↥S') \ ∅) ?_
          rw [refFac, if_neg hq]
        rw [frozen, this, mul_zero, zero_mul]
      · have : cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) = 0 := by simp only [cellAway]; rw [if_neg h]
        rw [frozen, Vfun, this, zero_mul, mul_zero, mul_zero]
    rw [hzero, zero_mul, norm_zero]
    by_cases hmem : g ∈ NK
    · rw [Set.indicator_of_mem hmem]; exact abs_nonneg M
    · rw [Set.indicator_of_notMem hmem]

end Base

section Swap

variable {SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))} {L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ} {M : ℝ}
  (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
  (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
  (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
include hLone hLphase hLlc

theorem integrable_frozen_univ [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] (σ₀ : ℝ)
    (hloc : ∀ p : ↥S', letI := localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ)); haveI := borelSpace_localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
      ∃ (μ₂ : Measure (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) (_ : μ₂.IsHaarMeasure)
        (μN₂ : Measure ↥(unipL (p : HeightOneSpectrum (𝓞 ℚ)))) (_ : μN₂.IsHaarMeasure),
        (∫⁻ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), ‖(aFac SQ L p y * 1) *
            ((modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
              (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) ^ ((σ₀ : ℂ) - 1 / 2)‖ₑ
          ∂(μ₂.withDensity (HaarQuotient.density (unipL (p : HeightOneSpectrum (𝓞 ℚ))) μN₂))) < ⊤) :
    Integrable (fun g : finiteAdelicGL2Subgroup ℚ => frozen SQ S' L M Finset.univ (g : AdelicGL2 (𝓞 ℚ) ℚ) * cw (σ₀ : ℂ) g)
      (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical
  set ν := μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin) with hν
  suffices h : ∀ T : Finset ↥S', Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
      frozen SQ S' L M T (g : AdelicGL2 (𝓞 ℚ) ℚ) * cw (σ₀ : ℂ) g) ν from h _
  intro T
  induction T using Finset.induction_on with
  | empty => exact integrable_base hLone hLphase hLlc μf μNFin σ₀
  | insert p T hpT ih =>
    letI : MeasurableSpace (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
    haveI : BorelSpace (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (p : HeightOneSpectrum (𝓞 ℚ))
    obtain ⟨μ₂, hμ₂, μN₂, hμN₂, hfin⟩ := hloc p

    let W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun X =>
      (∏ q ∈ T, aFac SQ L q (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) X)) *
        (∏ q ∈ Finset.univ \ insert p T, refFac q (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) X)) * Vfun S' L M X
    let one : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun _ => 1
    let onel : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ := fun _ => 1
    have hsdiff : Finset.univ \ T = insert p (Finset.univ \ insert p T) := by
      ext q
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases hq : q = p
        · exact Or.inl hq
        · exact Or.inr (fun h' => h'.elim hq h)
      · rintro (rfl | h)
        · exact hpT
        · exact fun h' => h (Or.inr h')
    have hp' : p ∉ Finset.univ \ insert p T := by simp

    have hfrT : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ, frozen SQ S' L M T X = refFac (p : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X := by
      intro X; simp only [frozen, W', hsdiff, Finset.prod_insert hp']; ring
    have hfrT' : ∀ X : AdelicGL2 (𝓞 ℚ) ℚ, frozen SQ S' L M (insert p T) X = aFac SQ L p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X := by
      intro X; simp only [frozen, W', Finset.prod_insert hpT]; ring

    have hne : ∀ q : ↥S', q ≠ p → (q : HeightOneSpectrum (𝓞 ℚ)) ≠ p := fun q hq h => hq (Subtype.ext h)
    have hW' : ∀ (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (X : AdelicGL2 (𝓞 ℚ) ℚ),
        W' (X * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = W' X := by
      intro x X
      have e1 : ∏ q ∈ T, aFac SQ L q (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (X * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x)) =
          ∏ q ∈ T, aFac SQ L q (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) X) := by
        refine Finset.prod_congr rfl fun q hq => ?_
        rw [map_mul, localAt_placeEmbed_of_ne _ (hne q (fun h => hpT (h ▸ hq))), mul_one]
      have e2 : ∏ q ∈ Finset.univ \ insert p T, refFac (q : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (X * placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x)) =
          ∏ q ∈ Finset.univ \ insert p T, refFac (q : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) X) := by
        refine Finset.prod_congr rfl fun q hq => ?_
        have hq' : q ≠ p := fun h => by simp [h] at hq
        rw [map_mul, localAt_placeEmbed_of_ne _ (hne q hq'), mul_one]
      simp only [W', e1, e2, Vfun_mul_placeEmbed p.2 x X]
    have hN' : ∀ (n : ↥RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        ‖W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
            one ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
          ‖W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * one (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ := by
      intro n g
      obtain ⟨t, ht⟩ := eq_unipotentGL2_of_mem_adelicUnipotent (coe_finUnipotent_mem n)
      have hloc' : ∀ q : ↥S', localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
          unipotent (t.2 q) * localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        intro q; rw [Subgroup.coe_mul, map_mul, ht, localAt_unipotentGL2, unipotent_eq_unipotentGL2]
      simp only [W', one, mul_one, norm_mul, norm_prod, hloc', aFac_unipotent_mul hLphase, refFac_unipotent_mul,
        norm_Vfun_unipotent_mul hLone hLphase]
    have hn : ∀ (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        ‖aFac SQ L p (unipotent x * y) * onel (unipotent x * y)‖ = ‖aFac SQ L p y * onel y‖ := by
      intro x y; simp only [onel, mul_one, aFac_unipotent_mul hLphase]
    have hn₀ : ∀ (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        ‖refFac (p : HeightOneSpectrum (𝓞 ℚ)) (unipotent x * y) * onel (unipotent x * y)‖ = ‖refFac (p : HeightOneSpectrum (𝓞 ℚ)) y * onel y‖ := by
      intro x y; simp only [onel, mul_one, refFac_unipotent_mul]

    have hcont : ∀ q : ↥S', Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
        refFac (q : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) := fun q => by
      letI : MeasurableSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      haveI : BorelSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      exact (measurable_refFac (q : HeightOneSpectrum (𝓞 ℚ))).comp (continuous_projAt (q : HeightOneSpectrum (𝓞 ℚ))).measurable
    have hameas : ∀ q : ↥S', Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
        aFac SQ L q (localAt ℚ (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)) := fun q => by
      letI : MeasurableSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      haveI : BorelSpace (GL (Fin 2) ((q : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) := borelSpace_localGLBorel ℚ (q : HeightOneSpectrum (𝓞 ℚ))
      exact (measurable_aFac hLlc (q : HeightOneSpectrum (𝓞 ℚ))).comp (continuous_projAt (q : HeightOneSpectrum (𝓞 ℚ))).measurable
    have hWm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g := by
      refine ((Finset.measurable_prod _ fun q _ => hameas q).mul (Finset.measurable_prod _ fun q _ => hcont q)).mul
        (measurable_Vfun_coe hLone hLlc)
    have hWFm' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g * one g := by
      simp only [one, mul_one]; exact hWm
    have hWFm : Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
        (fun X => aFac SQ L p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X) g *
          (fun X => onel (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * one X) g := by
      simp only [one, onel, mul_one]; exact (hameas p).mul hWm

    have key := LanglandsTunnell.RankinSelberg.integrable_finCell_of_integrable_of_factorsAt (p : HeightOneSpectrum (𝓞 ℚ)) μf μNFin
      (fun X => aFac SQ L p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X)
      (fun X => onel (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * one X)
      (fun X => refFac (p : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X)
      (fun X => onel (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * one X)
      W' one (aFac SQ L p) onel (refFac (p : HeightOneSpectrum (𝓞 ℚ))) onel
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hW' (fun _ _ => rfl) hN' hn hn₀ hWFm' hWFm ((σ₀ : ℂ)) μ₂ μN₂
      (by simp only [onel, mul_one]; exact measurable_aFac hLlc _) (by simp only [onel, mul_one]; exact measurable_refFac _)
    have hint : Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
        ((fun X : AdelicGL2 (𝓞 ℚ) ℚ => refFac (p : HeightOneSpectrum (𝓞 ℚ)) (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * W' X) g *
          (fun X : AdelicGL2 (𝓞 ℚ) ℚ => onel (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) X) * one X) g) *
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ ((σ₀ : ℂ) - 1 / 2)) ν := by
      refine ih.congr (Filter.Eventually.of_forall fun g => ?_)
      simp only [one, onel, mul_one, hfrT, cw]
    have hne0 := lintegral_refFac_ne_zero (p := (p : HeightOneSpectrum (𝓞 ℚ))) ((σ₀ : ℂ)) μ₂ μN₂
    have hfin' : (∫⁻ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), ‖(aFac SQ L p y * onel y) *
        ((modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
          (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) ^ ((σ₀ : ℂ) - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipL (p : HeightOneSpectrum (𝓞 ℚ))) μN₂))) < ⊤ := by
      simpa only [onel] using hfin
    have hne0' : (∫⁻ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), ‖(refFac (p : HeightOneSpectrum (𝓞 ℚ)) y * onel y) *
        ((modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
          (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) ^ ((σ₀ : ℂ) - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipL (p : HeightOneSpectrum (𝓞 ℚ))) μN₂))) ≠ 0 := by
      simpa only [onel] using hne0
    have hres := key hint hne0' hfin'
    refine hres.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [one, onel, mul_one, hfrT', cw]

end Swap

section Main

variable {SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))} (hSS' : SQ ⊆ S')
  {L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ}
  (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
  (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
  (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
  (hLgauge : ∀ v ∈ S', ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → L v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖L v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
  {B : finiteAdelicGL2Subgroup ℚ → ℂ} (hBm : Measurable B) {M r : ℝ}
  (hB : ∀ g : finiteAdelicGL2Subgroup ℚ, ‖B g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r)
include hSS' hLlc hLphase hLone hLgauge hBm hB

theorem main [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          (bigCell SQ).indicator B g *
            (bigCell SQ).indicator (fun g => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) g *
            cw s g)
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  classical

  letI : ∀ p : HeightOneSpectrum (𝓞 ℚ), MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => localGLBorel ℚ p
  haveI : ∀ p : HeightOneSpectrum (𝓞 ℚ), BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => borelSpace_localGLBorel ℚ p
  haveI : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => locallyCompactSpace_localGL ℚ p
  haveI : ∀ p : HeightOneSpectrum (𝓞 ℚ), LocallyCompactSpace ↥(unipL p) := fun p =>
    (isClosed_unipL p).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ₂ : ∀ p : HeightOneSpectrum (𝓞 ℚ), Measure (GL (Fin 2) (p.adicCompletion ℚ)) := fun p => Measure.haar
  let μN₂ : ∀ p : HeightOneSpectrum (𝓞 ℚ), Measure ↥(unipL p) := fun p => Measure.haar
  have hC := fun p : ↥S' =>
    LanglandsTunnell.RankinSelberg.exists_forall_lintegral_enorm_comp_iotaGL_mul_modulus_cpow_lt_top_of_gauge (p : HeightOneSpectrum (𝓞 ℚ))
      (L p) (hLlc p) (hLphase p) (hLgauge p p.2) (μ₂ p) (μN₂ p)
  choose σloc hσloc using hC
  refine ⟨(∑ p : ↥S', |σloc p|) - r, fun s hs => ?_⟩
  set σ₀ : ℝ := s.re + r with hσ₀
  have hσp : ∀ p : ↥S', σloc p < σ₀ := by
    intro p
    have h1 : σloc p ≤ |σloc p| := le_abs_self _
    have h2 : |σloc p| ≤ ∑ q : ↥S', |σloc q| := Finset.single_le_sum (fun q _ => abs_nonneg (σloc q)) (Finset.mem_univ p)
    rw [hσ₀]; linarith
  set ν := μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin) with hν

  have hloc : ∀ p : ↥S',
      ∃ (μ₂' : Measure (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) (_ : μ₂'.IsHaarMeasure)
        (μN₂' : Measure ↥(unipL (p : HeightOneSpectrum (𝓞 ℚ)))) (_ : μN₂'.IsHaarMeasure),
        (∫⁻ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), ‖(aFac SQ L p y * 1) *
            ((modulus ((Matrix.GeneralLinearGroup.det y : ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)ˣ) :
              (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) : ℝ) : ℂ) ^ ((σ₀ : ℂ) - 1 / 2)‖ₑ
          ∂(μ₂'.withDensity (HaarQuotient.density (unipL (p : HeightOneSpectrum (𝓞 ℚ))) μN₂'))) < ⊤ := by
    intro p
    refine ⟨μ₂ p, inferInstance, μN₂ p, inferInstance, ?_⟩
    by_cases hp : (p : HeightOneSpectrum (𝓞 ℚ)) ∈ SQ
    · have h1 : ∀ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), aFac SQ L p y * 1 = L p (iotaGL y) := fun y => by
        rw [mul_one, aFac, cfac, if_pos hp, one_mul]
      simp only [h1]
      exact hσloc p ((σ₀ : ℂ)) (by rw [Complex.ofReal_re]; exact hσp p)
    · have h1 : ∀ y : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), aFac SQ L p y * 1 = refFac p y * L p (iotaGL y) * 1 := fun y => by
        rw [aFac, cfac, if_neg hp, refFac]
      simp only [h1]
      exact lintegral_locCell_mul_lt_top (L p) (hLlc p) (hLphase p) _ (μ₂ p) (μN₂ p)
  have hQ := integrable_frozen_univ (SQ := SQ) (M := M) hLone hLphase hLlc μf μNFin σ₀ hloc

  have hmeas : Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      (bigCell SQ).indicator B g *
        (bigCell SQ).indicator (fun g => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) g * cw s g :=
    ((hBm.indicator (measurableSet_bigCell SQ)).mul
      ((continuous_finprod_fFam_coe hLone hLlc).measurable.indicator (measurableSet_bigCell SQ))).mul (measurable_cw s)
  refine hQ.norm.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)

  rw [indicator_bigCell_eq hSS', indicator_bigCell_eq hSS', finprod_fFam_eq hLone]
  set c : ℝ := ‖∏ p ∈ S', cfac SQ p (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))‖ with hc
  set w : ℝ := ‖cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ with hw
  set ℓ : ℝ := ‖∏ v ∈ S', L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))‖ with hℓ
  set e : ℝ := ‖Efun S' L (g : AdelicGL2 (𝓞 ℚ) ℚ)‖ with he
  set N : ℝ := ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) with hN
  have hNpos : 0 < N := ideleNorm_pos _
  have hc1 : c ≤ 1 := by
    rw [hc, norm_prod]
    exact Finset.prod_le_one (fun p _ => norm_nonneg _) fun p _ => norm_cfac_le_one p _
  have hw1 : w ≤ 1 := norm_cellAway_le_one _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hw0 : 0 ≤ w := norm_nonneg _
  have hMle : ‖B g‖ ≤ |M| * N ^ r :=
    (hB g).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg hNpos.le _))

  have hL : ‖(∏ p ∈ S', cfac SQ p (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) * cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) * B g *
      ((∏ p ∈ S', cfac SQ p (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) * cellAway S' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
        ((∏ v ∈ S', L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) * Efun S' L (g : AdelicGL2 (𝓞 ℚ) ℚ))) * cw s g‖ =
      (c * c) * (w * w) * ‖B g‖ * ℓ * e * N ^ (s.re - 1 / 2) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_cw]
    ring

  have hprod : ‖∏ p : ↥S', aFac SQ L p (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ))‖ = c * ℓ := by
    rw [hc, hℓ, ← norm_mul, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort S']
    rfl
  have hR : ‖frozen SQ S' L M Finset.univ (g : AdelicGL2 (𝓞 ℚ) ℚ) * cw (σ₀ : ℂ) g‖ = c * ℓ * |M| * w * e * N ^ (s.re + r - 1 / 2) := by
    rw [norm_mul, frozen, Finset.sdiff_self, Finset.prod_empty, mul_one, norm_mul, hprod, Vfun, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, norm_cw, Complex.ofReal_re]
    ring
  rw [hL, hR]
  have hsplit : N ^ (s.re + r - 1 / 2) = N ^ r * N ^ (s.re - 1 / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  rw [hsplit]
  have hcc : c * c ≤ c := mul_le_of_le_one_left hc0 hc1
  have hww : w * w ≤ w := mul_le_of_le_one_left hw0 hw1
  have hℓ0 : 0 ≤ ℓ := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  calc c * c * (w * w) * ‖B g‖ * ℓ * e * N ^ (s.re - 1 / 2)
      ≤ c * w * (|M| * N ^ r) * ℓ * e * N ^ (s.re - 1 / 2) := by
        gcongr
    _ = c * ℓ * |M| * w * e * (N ^ r * N ^ (s.re - 1 / 2)) := by ring

end Main

end KcBigCellEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge.KcBigCellEngine"

open KcBigCellEngine in
theorem solution
    (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')

    (L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
    (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
    (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' →
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
    (hLgauge : ∀ v ∈ S', ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → L v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖L v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (B : finiteAdelicGL2Subgroup ℚ → ℂ) (hBm : Measurable B)
    (hBgr : ∃ M r : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖B g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r)

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator B g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by
  obtain ⟨M, r, hB⟩ := hBgr
  exact KcBigCellEngine.main hSS' hLlc hLphase hLone hLgauge hBm hB μf μNFin

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge (solution)
