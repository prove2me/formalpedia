-- Prove2me | solution 1 for NumberField.LevelArith.hasBrauerLocalInvAt_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/98eada00-4d92-53ef-9d60-2ed7e8a3bcac

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
import Theorems.Thm_NumberField_IdeleLocalInv_eq_of_hasLocalInv
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add.NumberField.LevelArith TensorProduct Pointwise"

p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add.NumberField"
open scoped NumberField.PlaceDecomp

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.toUnitsRep SUnits.val PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv placesOverPrimes LevelArith.hasLocalInv_of_hasLocalInv_of_le IdeleLocalInv.eq_of_hasLocalInv LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelFieldEquiv coe_levelFieldEquiv placesOverPrimes placesOverPrimesFinset sUnitsMaxRep HasBrauerLocalInvAt hasLocalInv_of_hasLocalInv_of_le exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace ValueAdd
p2m_open "NumberField.LevelArith NumberField"

section Cohomology

variable {G : Type} [Group G]

theorem map_top_subtype_injective (B : Rep ℤ G) :
    Function.Injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom := by
  let eT : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom
  have key : groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2 ≫
      groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2 = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := B) (n := 2)
  have hleft : ∀ y : groupCohomology B 2,
      (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2).hom
        ((groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom y) = y := by
    intro y
    have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
    exact hy
  exact Function.LeftInverse.injective hleft

variable {A B : Rep ℤ G} (θ : B ⟶ A) (θ' : A ⟶ B) (u : groupCohomology B 2)

theorem exists_eq_zsmul_map_of_span (hθ'θ : θ' ≫ θ = 𝟙 A)
    (hspan : Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} = ⊤)
    (c : groupCohomology A 2) :
    ∃ m : ℤ, c = m • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by
  have hback : ∀ y : groupCohomology A 2,
      (groupCohomology.map (MonoidHom.id G) θ 2).hom ((groupCohomology.map (MonoidHom.id G) θ' 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
    simp only [hθ'θ, groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  set X' := (groupCohomology.map (MonoidHom.id G) θ' 2).hom c with hX'
  have hmem : (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom X' ∈
      Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} := by
    rw [hspan]; trivial
  obtain ⟨m₀, hm₀⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨m₀, ?_⟩
  have hXu : X' = m₀ • u := by
    apply map_top_subtype_injective B
    rw [map_zsmul, ← hm₀]
    exact int_smul_eq_zsmul _ m₀ _
  calc c = (groupCohomology.map (MonoidHom.id G) θ 2).hom X' := (hback _).symm
    _ = m₀ • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by rw [hXu, map_zsmul]

end Cohomology

section Solvable
open ExtCitation.LocalLevel

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable

section Add

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
  [MulDistribMulAction (K ≃ₐ[E] K) (NumberField.AdeleRing (𝓞 K) K)ˣ]
  (hactI : ∀ (g : K ≃ₐ[E] K) (y : (NumberField.AdeleRing (𝓞 K) K)ˣ), g • y = D.unitsAct g y)

theorem exists_inverse_unitsTransport (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {q : ℕ} [Fact q.Prime]
    (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K w) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L')ˣ]
    (Φ : w.adicCompletion K ≃+* L')
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L')) :
    ∃ θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L')ˣ, θ' ≫ θ = 𝟙 _ := by
  let ΦM : (w.adicCompletion K)ˣ →* (↥L')ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (m : (w.adicCompletion K)ˣ), ΦM (g • m) = g • ΦM m := by
    intro g m
    apply Units.ext
    rw [hΦ₂ g (ΦM m)]
    show Φ ((g • m : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = g • Φ (m : (w.adicCompletion K))
    rw [NumberField.PlaceDecomp.coe_smul_units, hΦ₃ g]
  refine ⟨M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, ?_⟩
  refine Rep.hom_ext ?_
  ext z
  rw [Rep.hom_comp, Rep.hom_id]
  show θ.hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
  rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
  change Additive.ofMul (Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z))))) = Additive.ofMul (Additive.toMul z)
  congr 1
  apply Units.ext
  have h : ((Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z)))) : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) =
      Φ.symm ((ΦM (Additive.toMul z) : (↥L')ˣ) : ↥L') := hθ (ΦM (Additive.toMul z))
  refine h.trans ?_
  show Φ.symm (Φ ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))) = ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))
  exact Φ.symm_apply_apply _

include hactI in

theorem hasLocalInv_add (x y : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (NumberField.AdeleRing (𝓞 K) K)ˣ) 2)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (t t' : AddCircle (1 : ℚ))
    (hx : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t) (hy : NumberField.IdeleLocalInv.HasLocalInv E K D hactI y v t') :
    NumberField.IdeleLocalInv.HasLocalInv E K D hactI (x + y) v (t + t') := by
  obtain ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n, hcoord, ht⟩ := hx
  haveI := hq
  haveI := hfd
  letI := hsma
  haveI := hfs
  letI := hmda
  haveI := hfd₀

  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w) := by
    exact isSolvable_layer q L' ↥(NumberField.PlaceDecomp.decomp E K w) hΦ1 K₀ hbase
  obtain ⟨-, -, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp E K w) hΦ1 hΦ2 hsolv K₀ hbase u' hu'
  obtain ⟨θ', hθ'θ⟩ := exists_inverse_unitsTransport E K w L' Φ hΦ2 hΦ3 θ hθ
  obtain ⟨m, hm⟩ := exists_eq_zsmul_map_of_span θ θ' u' hθ'θ (hspan ⊤)
    ((groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom y)
  have hy' : NumberField.IdeleLocalInv.HasLocalInv E K D hactI y v
      ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) :=
    ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', m, hm, rfl⟩
  have htm : ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = t' :=
    NumberField.IdeleLocalInv.eq_of_hasLocalInv E K D hactI y v _ _ hy' hy
  have hcoord' : (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom (x + y) =
      (n + m) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u' := by
    rw [map_add, hcoord, hm, add_zsmul]
  refine ⟨prG, hpr, w, hw, q, hq, hqw, L', hfd, hsma, hfs, hmda, Φ, hΦ1, hΦ2, hΦ3, K₀, hfd₀, hbase, θ, hθ, u', hu', n + m, hcoord', ?_⟩
  rw [ht, ← htm, ← AddCircle.coe_add]
  push_cast
  rw [add_div]

end Add

end NumberField.LevelArith.ValueAdd

set_option maxHeartbeats 6400000 in
open NumberField.LevelArith.ValueAdd in
open scoped _root_.NumberField _root_.P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add.NumberField in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a b : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (t t' : AddCircle (1 : ℚ))
    (ha : HasBrauerLocalInvAt p S L a v t) (hb : HasBrauerLocalInvAt p S L b v t') :
    HasBrauerLocalInvAt p S L (a + b) v (t + t') := by

  obtain ⟨Fa, hLFa, hfda, hna, hgala, hFa, ιa, hιa, φa, hbija, hvala, Da, insta, hacta, ja, hja, fa, ha_infl, ha_loc⟩ := ha
  obtain ⟨Fb, hLFb, hfdb, hnb, hgalb, hFb, ιb, hιb, φb, hbijb, hvalb, Db, instb, hactb, jb, hjb, fb, hb_infl, hb_loc⟩ := hb
  haveI := hfda; haveI := hna; haveI := hgala; haveI := hfdb; haveI := hnb; haveI := hgalb

  obtain ⟨F, hFabF, hF, hnormF⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (Fa ⊔ Fb) (hFa.sup hFb)
  haveI := hnormF
  haveI : FiniteDimensional ℚ ↥F := hF.1
  have hFaF : Fa ≤ F := le_sup_left.trans hFabF
  have hFbF : Fb ≤ F := le_sup_right.trans hFabF
  have hLF : L ≤ F := hLFa.trans hFaF

  haveI : IsGalois ↥L ↥(levelField L F hLF) := by
    haveI : Normal ℚ ↥(levelField L F hLF) := Normal.of_algEquiv
      (AlgEquiv.ofRingEquiv (f := levelFieldEquiv L F hLF) (fun r => by apply Subtype.ext; rw [coe_levelFieldEquiv]; rfl))
    haveI : IsGalois ℚ ↥(levelField L F hLF) := IsGalois.mk
    exact IsGalois.tower_top_of_isGalois ℚ ↥L ↥(levelField L F hLF)

  have hUa : F.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ Fa.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hFaF)
  let πa : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype →*
      ↥L.fixingSubgroup ⧸ Fa.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    QuotientGroup.map _ _ (MonoidHom.id _) hUa
  have hinva : Representation.invariants ((sUnitsMaxRep S L).ρ.comp (Fa.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) ≤
      Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
    intro m hm u
    exact hm ⟨u.1, hUa u.2⟩
  let ψa : Rep.res πa ((sUnitsMaxRep S L).quotientToInvariants (Fa.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨Submodule.inclusion hinva, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      refine LinearMap.ext fun z => Subtype.ext ?_
      rfl⟩
  obtain ⟨fa', hffa⟩ : ∃ fa' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g h : ↥L.fixingSubgroup,
      ((fa' ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
      = ((fa ((g : ↥L.fixingSubgroup ⧸ Fa.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ Fa.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := by
    refine ⟨mapCocycles₂ πa ψa fa, fun g h => ?_⟩
    show (((mapCocycles₂ πa ψa fa : cocycles₂ _) : _ → _) ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : _)) : (sUnitsMaxRep S L).quotientToInvariants _).1 = _
    rw [coe_mapCocycles₂]
    rfl
  clear ψa hinva πa

  have hUb : F.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ Fb.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hFbF)
  let πb : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype →*
      ↥L.fixingSubgroup ⧸ Fb.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    QuotientGroup.map _ _ (MonoidHom.id _) hUb
  have hinvb : Representation.invariants ((sUnitsMaxRep S L).ρ.comp (Fb.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) ≤
      Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
    intro m hm u
    exact hm ⟨u.1, hUb u.2⟩
  let ψb : Rep.res πb ((sUnitsMaxRep S L).quotientToInvariants (Fb.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨Submodule.inclusion hinvb, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      refine LinearMap.ext fun z => Subtype.ext ?_
      rfl⟩
  obtain ⟨fb', hffb⟩ : ∃ fb' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g h : ↥L.fixingSubgroup,
      ((fb' ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
      = ((fb ((g : ↥L.fixingSubgroup ⧸ Fb.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ Fb.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := by
    refine ⟨mapCocycles₂ πb ψb fb, fun g h => ?_⟩
    show (((mapCocycles₂ πb ψb fb : cocycles₂ _) : _ → _) ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : _)) : (sUnitsMaxRep S L).quotientToInvariants _).1 = _
    rw [coe_mapCocycles₂]
    rfl
  clear ψb hinvb πb

  obtain ⟨ι, hι, φ, hbij, hval⟩ :=
    NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective S L F hLF hF
  obtain ⟨D⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F hLF)
  letI instI : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ := MulDistribMulAction.compHom _ D.unitsAct
  have hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y := fun _ _ => rfl
  let jK : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (↥(levelField L F hLF))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ :=
    M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))) (fun g u => by
      apply Units.ext
      show algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (g • (u : ↥(levelField L F hLF))) = D.act g (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (u : ↥(levelField L F hLF)))
      rw [D.compat]
      rfl)
  let j := NumberField.SUnits.toUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ≫ jK
  have hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y) :=
    fun y => rfl

  have ha' : NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ fa')) v.1 t :=
    NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le S L Fa hLFa hFa F hLF hF hFaF ιa hιa φa hbija hvala ι hι φ hbij hval
      Da hacta ja hja D hactI j hj fa fa' hffa v.1 t ha_loc
  have hb' : NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ fb')) v.1 t' :=
    NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le S L Fb hLFb hFb F hLF hF hFbF ιb hιb φb hbijb hvalb ι hι φ hbij hval
      Db hactb jb hjb D hactI j hj fb fb' hffb v.1 t' hb_loc

  have hsum : NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ (fa' + fb'))) v.1 (t + t') := by
    rw [map_add, map_add]
    exact hasLocalInv_add ↥L ↥(levelField L F hLF) D hactI _ _ v.1 t t' ha' hb'
  have e1 := groupCohomology.continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) Fa F hFa hF fa fa' hffa
  have e2 := groupCohomology.continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) Fb F hFb hF fb fb' hffb
  have e3 : (H2π ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) (fa' + fb') :
      groupCohomology.H2 ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) =
      H2π _ fa' + H2π _ fb' := map_add _ _ _
  have e4 : continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ fa' + H2π _ fb') =
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ fa') +
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ fb') := map_add _ _ _
  have hinfl : ((a + b : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) :
      continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) =
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ (fa' + fb')) :=
    (Submodule.coe_add a b).trans <| (congrArg₂ (· + ·) ha_infl hb_infl).trans <|
      (congrArg₂ (· + ·) e1 e2).symm.trans <| e4.symm.trans (congrArg _ e3.symm)
  exact ⟨F, hLF, inferInstance, inferInstance, inferInstance, hF, ι, hι, φ, hbij, hval, D, instI, hactI, j, hj, fa' + fb', hinfl, hsum⟩

end S_NumberField_LevelArith_hasBrauerLocalInvAt_add
end P2MW
export P2MW.S_NumberField_LevelArith_hasBrauerLocalInvAt_add (solution)
