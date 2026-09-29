-- Prove2me | solution 1 for LanglandsTunnell.exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ca907aed-95b7-5d89-a680-77da4341ae51

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
import Theorems.Thm_HeckeCharacter_exists_admitsModulus_of_continuous_of_isOfFinOrder
import Theorems.Thm_HeckeCharacter_raySymbol_apply_uniformizerIdele_eq_prod_archLocalChar_neg_one_of_admitsModulus
import Theorems.Thm_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj
import Theorems.Thm_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Deep.NTSupply NumberField.AdelicLevel NumberField.AdelicVolume LanglandsTunnell.P2.Artin LanglandsTunnell.Converse

open scoped nonZeroDivisors

noncomputable section

namespace DetInducedSol

section Quad

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

theorem finiteDimensional (h2 : Module.finrank F L = 2) : FiniteDimensional F L :=
  Module.finite_of_finrank_eq_succ h2

theorem isGalois (h2 : Module.finrank F L = 2) : IsGalois F L := by
  haveI := finiteDimensional h2
  haveI : Algebra.IsQuadraticExtension F L := ⟨h2⟩
  infer_instance

theorem card_gal (h2 : Module.finrank F L = 2) :
    haveI := finiteDimensional h2
    Fintype.card (L ≃ₐ[F] L) = 2 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]

theorem natCard_gal (h2 : Module.finrank F L = 2) : Nat.card (L ≃ₐ[F] L) = 2 := by
  haveI := finiteDimensional h2
  rw [Nat.card_eq_fintype_card, card_gal h2]

theorem exists_ne_one (h2 : Module.finrank F L = 2) : ∃ τ : L ≃ₐ[F] L, τ ≠ 1 := by
  haveI := finiteDimensional h2
  have h : 1 < Fintype.card (L ≃ₐ[F] L) := by rw [card_gal h2]; norm_num
  haveI := Fintype.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem eq_one_or_eq (h2 : Module.finrank F L = 2) {τ : L ≃ₐ[F] L} (hτ : τ ≠ 1)
    (σ : L ≃ₐ[F] L) : σ = 1 ∨ σ = τ := by
  classical
  haveI := finiteDimensional h2
  have hcard : (Finset.univ : Finset (L ≃ₐ[F] L)).card = 2 := by
    rw [Finset.card_univ, card_gal h2]
  obtain ⟨x, y, -, hxy⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ g : L ≃ₐ[F] L, g = x ∨ g = y := fun g => by
    have := Finset.mem_univ g
    rw [hxy, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  rcases hmem 1 with h1 | h1 <;> rcases hmem τ with hτ' | hτ' <;> rcases hmem σ with hσ | hσ
  all_goals first
    | exact absurd (hτ'.trans h1.symm) hτ
    | exact Or.inl (hσ.trans h1.symm)
    | exact Or.inr (hσ.trans hτ'.symm)

theorem mul_self_eq_one (h2 : Module.finrank F L = 2) (σ : L ≃ₐ[F] L) : σ * σ = 1 := by
  by_cases hσ : σ = 1
  · rw [hσ, mul_one]
  · rcases eq_one_or_eq h2 hσ (σ * σ) with h | h
    · exact h
    · exact absurd (mul_left_cancel (h.trans (mul_one σ).symm)) hσ

theorem isMulCommutative (h2 : Module.finrank F L = 2) : IsMulCommutative (L ≃ₐ[F] L) := by
  obtain ⟨τ, hτ⟩ := exists_ne_one h2
  refine ⟨⟨fun a b => ?_⟩⟩
  rcases eq_one_or_eq h2 hτ a with ha | ha <;> rcases eq_one_or_eq h2 hτ b with hb | hb <;>
    simp [ha, hb]

def theta (h2 : Module.finrank F L = 2) : (L ≃ₐ[F] L) →* ℂˣ := by
  classical
  exact
  { toFun := fun σ => if σ = 1 then 1 else -1
    map_one' := if_pos rfl
    map_mul' := fun a b => by
      obtain ⟨τ, hτ⟩ := exists_ne_one h2
      rcases eq_one_or_eq h2 hτ a with ha | ha <;> rcases eq_one_or_eq h2 hτ b with hb | hb
      · subst ha; subst hb; simp
      · subst ha; simp
      · subst hb; simp
      · subst ha; subst hb
        rw [mul_self_eq_one h2, if_pos rfl, if_neg hτ, neg_mul_neg, one_mul] }

open scoped Classical in
theorem theta_apply (h2 : Module.finrank F L = 2) (σ : L ≃ₐ[F] L) :
    theta h2 σ = if σ = 1 then 1 else -1 := by
  unfold theta
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]

theorem theta_one (h2 : Module.finrank F L = 2) : theta h2 1 = 1 := map_one _

theorem theta_of_ne_one (h2 : Module.finrank F L = 2) {σ : L ≃ₐ[F] L} (hσ : σ ≠ 1) :
    theta h2 σ = -1 := by
  classical
  rw [theta_apply, if_neg hσ]

theorem coe_theta_of_ne_one (h2 : Module.finrank F L = 2) {σ : L ≃ₐ[F] L} (hσ : σ ≠ 1) :
    ((theta h2 σ : ℂˣ) : ℂ) = -1 := by
  rw [theta_of_ne_one h2 hσ, Units.val_neg, Units.val_one]

end Quad

section Local

open scoped Pointwise

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

omit [NumberField E] [NumberField M] in
theorem mem_primesOver_iff {v : HeightOneSpectrum (𝓞 E)} {Q : HeightOneSpectrum (𝓞 M)} :
    Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) ↔ Q.asIdeal.under (𝓞 E) = v.asIdeal :=
  ⟨fun h => h.2.over.symm, fun h => ⟨Q.isPrime, ⟨h.symm⟩⟩⟩

attribute [local instance] Ideal.Quotient.field in

theorem ncard_mul_inertiaDeg_eq_two (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    {Q : HeightOneSpectrum (𝓞 M)} (hQ : Q.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; Q.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    (v.asIdeal.primesOver (𝓞 M)).ncard * v.asIdeal.inertiaDeg' Q.asIdeal = 2 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : Q.asIdeal.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := Q.isMaximal
  haveI := v.isMaximal
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have h := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := M ≃ₐ[E] M) v.asIdeal Q.asIdeal
  rw [hI, Subgroup.card_bot, mul_one, natCard_gal h2] at h
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal Q.asIdeal]
  exact h

attribute [local instance] Ideal.Quotient.field in

theorem card_stabilizer_eq_inertiaDeg (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    {Q : HeightOneSpectrum (𝓞 M)} (hQ : Q.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; Q.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    haveI := finiteDimensional h2
    Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) Q.asIdeal) = v.asIdeal.inertiaDeg' Q.asIdeal := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : Q.asIdeal.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := Q.isMaximal
  haveI := v.isMaximal
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := M ≃ₐ[E] M) v.asIdeal Q.asIdeal, hI,
    Subgroup.card_bot, one_mul, Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal Q.asIdeal]

attribute [local instance] Ideal.Quotient.field in

theorem ramificationIdx_eq_one (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    {Q : HeightOneSpectrum (𝓞 M)} (hQ : Q.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; Q.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    Ideal.ramificationIdx' v.asIdeal Q.asIdeal = 1 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : Q.asIdeal.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := Q.isMaximal
  haveI := v.isMaximal
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q.asIdeal v.ne_bot,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q.asIdeal (M ≃ₐ[E] M),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[E] M) v.asIdeal Q.asIdeal, hI,
    Subgroup.card_bot]

theorem primesOver_eq_pair (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    {w' w'' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w'') (h' : w'.asIdeal.under (𝓞 E) = v.asIdeal)
    (h'' : w''.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; w'.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    v.asIdeal.primesOver (𝓞 M) = {w'.asIdeal, w''.asIdeal} ∧
      (v.asIdeal.primesOver (𝓞 M)).ncard = 2 := by
  haveI := v.isMaximal
  have hfin : (v.asIdeal.primesOver (𝓞 M)).Finite := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)
  have hsub : ({w'.asIdeal, w''.asIdeal} : Set (Ideal (𝓞 M))) ⊆ v.asIdeal.primesOver (𝓞 M) := by
    intro P hP
    rcases hP with rfl | rfl
    · exact mem_primesOver_iff.mpr h'
    · exact mem_primesOver_iff.mpr h''
  have hne' : w'.asIdeal ≠ w''.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have hge : 2 ≤ (v.asIdeal.primesOver (𝓞 M)).ncard := by
    rw [← Set.ncard_pair hne']
    exact Set.ncard_le_ncard hsub hfin
  have hkey := ncard_mul_inertiaDeg_eq_two h2 h' hI
  haveI : w'.asIdeal.LiesOver v.asIdeal := ⟨h'.symm⟩
  have hfpos : 0 < v.asIdeal.inertiaDeg' w'.asIdeal := Ideal.inertiaDeg'_pos v.asIdeal w'.asIdeal
  have hle : (v.asIdeal.primesOver (𝓞 M)).ncard ≤ 2 := by
    calc (v.asIdeal.primesOver (𝓞 M)).ncard ≤ (v.asIdeal.primesOver (𝓞 M)).ncard *
        v.asIdeal.inertiaDeg' w'.asIdeal := Nat.le_mul_of_pos_right _ hfpos
      _ = 2 := hkey
  have hcard : (v.asIdeal.primesOver (𝓞 M)).ncard = 2 := le_antisymm hle hge
  refine ⟨(Set.eq_of_subset_of_ncard_le hsub ?_ hfin).symm, hcard⟩
  rw [hcard, Set.ncard_pair hne']

theorem inertiaDeg_eq_one_of_ncard_eq_two (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    (hcard : (v.asIdeal.primesOver (𝓞 M)).ncard = 2)
    {Q : HeightOneSpectrum (𝓞 M)} (hQ : Q.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; Q.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    v.asIdeal.inertiaDeg' Q.asIdeal = 1 := by
  have hkey := ncard_mul_inertiaDeg_eq_two h2 hQ hI
  rw [hcard] at hkey
  omega

theorem primesOver_eq_singleton (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    {w' : HeightOneSpectrum (𝓞 M)} (h' : w'.asIdeal.under (𝓞 E) = v.asIdeal)
    (hf : v.asIdeal.inertiaDeg' w'.asIdeal = 2)
    (hI : haveI := finiteDimensional h2; w'.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    v.asIdeal.primesOver (𝓞 M) = {w'.asIdeal} := by
  have hkey := ncard_mul_inertiaDeg_eq_two h2 h' hI
  rw [hf] at hkey
  have hcard : (v.asIdeal.primesOver (𝓞 M)).ncard = 1 := by omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcard
  have hmem : w'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := mem_primesOver_iff.mpr h'
  rw [ha, Set.mem_singleton_iff] at hmem
  rw [ha, hmem]

theorem artinFrob_eq_one_of_ncard_eq_two (h2 : Module.finrank E M = 2) {v : HeightOneSpectrum (𝓞 E)}
    (hcard : (v.asIdeal.primesOver (𝓞 M)).ncard = 2)
    (hI : haveI := finiteDimensional h2; ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.under (𝓞 E) = v.asIdeal →
      Q.inertia (M ≃ₐ[E] M) = ⊥) :
    haveI := finiteDimensional h2; haveI := isGalois h2
    artinFrob E M v = 1 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  set Q₀ : HeightOneSpectrum (𝓞 M) := ⟨primeAbove E M v, inferInstance, primeAbove_ne_bot E M v⟩ with hQ₀
  have hQ₀v : Q₀.asIdeal.under (𝓞 E) = v.asIdeal := under_primeAbove E M v
  have hIQ : Q₀.asIdeal.inertia (M ≃ₐ[E] M) = ⊥ := hI _ Q₀.isPrime hQ₀v
  have hf : v.asIdeal.inertiaDeg' Q₀.asIdeal = 1 := inertiaDeg_eq_one_of_ncard_eq_two h2 hcard hQ₀v hIQ
  have hstab : Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) Q₀.asIdeal) = 1 := by
    rw [card_stabilizer_eq_inertiaDeg h2 hQ₀v hIQ, hf]
  have hbot : MulAction.stabilizer (M ≃ₐ[E] M) Q₀.asIdeal = ⊥ := Subgroup.eq_bot_of_card_eq _ hstab
  have hmem : artinFrob E M v ∈ MulAction.stabilizer (M ≃ₐ[E] M) Q₀.asIdeal :=
    (isArithFrobAt_artinFrob E M v).mem_stabilizer
  rw [hbot] at hmem
  exact Subgroup.mem_bot.mp hmem

attribute [local instance] Ideal.Quotient.field in

theorem artinFrob_ne_one_of_inertiaDeg_eq_two (h2 : Module.finrank E M = 2)
    {v : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)}
    (h' : w'.asIdeal.under (𝓞 E) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w'.asIdeal = 2)
    (hI : haveI := finiteDimensional h2; w'.asIdeal.inertia (M ≃ₐ[E] M) = ⊥) :
    haveI := finiteDimensional h2; haveI := isGalois h2
    artinFrob E M v ≠ 1 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  intro hone

  have hsing := primesOver_eq_singleton h2 h' hf hI
  have hmem : primeAbove E M v ∈ v.asIdeal.primesOver (𝓞 M) :=
    ⟨inferInstance, primeAbove_liesOver E M v⟩
  rw [hsing, Set.mem_singleton_iff] at hmem
  have hf' : v.asIdeal.inertiaDeg' (primeAbove E M v) = 2 := by rw [hmem]; exact hf

  haveI := v.isMaximal
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _
  have hfin : Module.finrank (𝓞 E ⧸ v.asIdeal) (𝓞 M ⧸ primeAbove E M v) = 2 := by
    rw [← Ideal.inertiaDeg_algebraMap]; exact hf'

  have hFrob : IsArithFrobAt (𝓞 E) (1 : M ≃ₐ[E] M) (primeAbove E M v) := by
    rw [← hone]; exact isArithFrobAt_artinFrob E M v
  have hq : Nat.card (𝓞 E ⧸ (primeAbove E M v).under (𝓞 E)) = Fintype.card (𝓞 E ⧸ v.asIdeal) := by
    rw [under_primeAbove, Nat.card_eq_fintype_card]
  have hpow : ∀ x : 𝓞 M, x - x ^ Fintype.card (𝓞 E ⧸ v.asIdeal) ∈ primeAbove E M v := by
    intro x
    have hx := hFrob x
    rw [hq] at hx
    simpa using hx
  have hid : FiniteField.frobeniusAlgHom (𝓞 E ⧸ v.asIdeal) (𝓞 M ⧸ primeAbove E M v) = 1 := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AlgHom.one_apply, FiniteField.coe_frobeniusAlgHom]
    show (Ideal.Quotient.mk (primeAbove E M v) x) ^ _ = Ideal.Quotient.mk (primeAbove E M v) x
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hpow x
  have hord := FiniteField.orderOf_frobeniusAlgHom (𝓞 E ⧸ v.asIdeal) (𝓞 M ⧸ primeAbove E M v)
  rw [hid, orderOf_one, hfin] at hord
  exact absurd hord (by norm_num)

end Local

section Tables

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

theorem raySymbol_mul_table (f g : HeightOneSpectrum (𝓞 E) → ℂˣ) (I : FractionalIdeal ((𝓞 E)⁰) E) :
    raySymbol E (fun v => f v * g v) I = raySymbol E f I * raySymbol E g I := by
  unfold raySymbol
  rw [← finprod_mul_distrib (hasFiniteMulSupport_raySymbol_factors E f I)
    (hasFiniteMulSupport_raySymbol_factors E g I)]
  exact finprod_congr fun v => mul_zpow _ _ _

open scoped IsMulCommutative in

theorem map_artinSymbol [IsGalois E M] [IsMulCommutative (M ≃ₐ[E] M)] (θ : (M ≃ₐ[E] M) →* ℂˣ)
    (𝔪 : Ideal (𝓞 E)) (x : coprimeToModulus E 𝔪) :
    θ (artinSymbol E M 𝔪 x) =
      raySymbol E (fun v => θ (artinFrob E M v))
        ((x : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) := by
  change θ (raySymbol E (artinFrob E M) _) = _
  unfold raySymbol
  rw [MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors E _ _)]
  simp_rw [map_zpow]
  rfl

def psiM (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 M)) : ℂˣ :=
  ξ (uniformizerIdele M w)

def extFrac (I : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 M)⁰) M :=
  ((I.map (algebraMap (𝓞 E) (𝓞 M)) : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M)

def Xi (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) : ℂˣ :=
  raySymbol M (psiM ξ) (extFrac (M := M) v.asIdeal)

omit [NumberField E] [NumberField M] in
theorem map_ne_bot {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : I.map (algebraMap (𝓞 E) (𝓞 M)) ≠ ⊥ := by
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_ringOfIntegers_injective E M)]
  exact hI

omit [NumberField E] in
theorem extFrac_ne_zero {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : extFrac (M := M) I ≠ 0 := by
  unfold extFrac
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact map_ne_bot hI

omit [NumberField E] [NumberField M] in
theorem extFrac_mul (I J : Ideal (𝓞 E)) : extFrac (M := M) (I * J) = extFrac I * extFrac J := by
  unfold extFrac
  rw [Ideal.map_mul, FractionalIdeal.coeIdeal_mul]

omit [NumberField E] [NumberField M] in
theorem extFrac_top : extFrac (M := M) (⊤ : Ideal (𝓞 E)) = 1 := by
  unfold extFrac
  rw [Ideal.map_top, FractionalIdeal.coeIdeal_top]

theorem raySymbol_one' {K : Type*} [Field K] [NumberField K] (f : HeightOneSpectrum (𝓞 K) → ℂˣ) :
    raySymbol K f (1 : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  unfold raySymbol
  simp [FractionalIdeal.count_one]

theorem raySymbol_Xi (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    raySymbol E (Xi ξ) ((I : FractionalIdeal ((𝓞 E)⁰) E)) = raySymbol M (psiM ξ) (extFrac I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ I hu =>
      rw [Ideal.isUnit_iff.mp hu, FractionalIdeal.coeIdeal_top, extFrac_top, raySymbol_one', raySymbol_one']
  | h₃ a p ha hp ih =>
      have hp0 : p ≠ ⊥ := hp.ne_zero
      set v : HeightOneSpectrum (𝓞 E) := ⟨p, (Ideal.prime_iff_isPrime hp0).mp hp, hp0⟩ with hv
      have hpv : p = v.asIdeal := rfl
      rw [FractionalIdeal.coeIdeal_mul, extFrac_mul,
        raySymbol_mul E (Xi ξ) (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hp0)
          (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha),
        raySymbol_mul M (psiM ξ) (extFrac_ne_zero hp0) (extFrac_ne_zero ha), ih ha, hpv,
        ← primeUnit_val, raySymbol_primeUnit]
      rfl

omit [NumberField E] [NumberField M] in
theorem extFrac_span_singleton (α : 𝓞 E) :
    extFrac (M := M) (Ideal.span {α}) =
      ((Ideal.span {algebraMap (𝓞 E) (𝓞 M) α} : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M) := by
  unfold extFrac
  rw [Ideal.map_span, Set.image_singleton]

omit [NumberField E] in

theorem count_extFrac (v : HeightOneSpectrum (𝓞 E)) (P : HeightOneSpectrum (𝓞 M)) :
    FractionalIdeal.count M P (extFrac (M := M) v.asIdeal) =
      (Ideal.ramificationIdx' v.asIdeal P.asIdeal : ℤ) := by
  unfold extFrac
  rw [FractionalIdeal.count_coe M P (map_ne_bot v.ne_bot),
    Ideal.count_associates_factors_eq (map_ne_bot v.ne_bot) P.isPrime P.ne_bot,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (map_ne_bot v.ne_bot) P.isPrime
      P.ne_bot]

theorem under_eq_of_count_ne_zero {v : HeightOneSpectrum (𝓞 E)} {P : HeightOneSpectrum (𝓞 M)}
    (h : FractionalIdeal.count M P (extFrac (M := M) v.asIdeal) ≠ 0) :
    P.asIdeal.under (𝓞 E) = v.asIdeal := by
  classical
  unfold extFrac at h
  rw [FractionalIdeal.count_coe M P (map_ne_bot v.ne_bot), Ne, Int.natCast_eq_zero, ← Ne,
    Associates.count_ne_zero_iff_dvd (map_ne_bot v.ne_bot) P.irreducible, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap] at h
  exact (v.isMaximal.eq_of_le (Ideal.IsPrime.under (𝓞 E) P.asIdeal).ne_top h).symm

theorem Xi_eq_prod (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 E)}
    (hI : haveI := finiteDimensional h2; ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.under (𝓞 E) = v.asIdeal →
      Q.inertia (M ≃ₐ[E] M) = ⊥)
    (s : Finset (HeightOneSpectrum (𝓞 M)))
    (hs : ∀ P : HeightOneSpectrum (𝓞 M), P ∈ s ↔ P.asIdeal.under (𝓞 E) = v.asIdeal) :
    Xi ξ v = ∏ P ∈ s, psiM ξ P := by
  unfold Xi raySymbol
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
  · refine Finset.prod_congr rfl fun P hP => ?_
    have hPv := (hs P).mp hP
    rw [count_extFrac, ramificationIdx_eq_one h2 hPv (hI _ P.isPrime hPv), Nat.cast_one, zpow_one]
  · intro P hP
    rw [Function.mem_mulSupport] at hP
    rw [Finset.mem_coe, hs]
    apply under_eq_of_count_ne_zero
    intro h0
    exact hP (by rw [h0, zpow_zero])

theorem Xi_eq_mul_of_split (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 E)} {w' w'' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w'')
    (h' : w'.asIdeal.under (𝓞 E) = v.asIdeal) (h'' : w''.asIdeal.under (𝓞 E) = v.asIdeal)
    (hI : haveI := finiteDimensional h2; ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.under (𝓞 E) = v.asIdeal →
      Q.inertia (M ≃ₐ[E] M) = ⊥) :
    Xi ξ v = psiM ξ w' * psiM ξ w'' := by
  classical
  have hpair := (primesOver_eq_pair h2 hne h' h'' (hI _ w'.isPrime h')).1
  rw [Xi_eq_prod h2 ξ hI ({w', w''} : Finset (HeightOneSpectrum (𝓞 M))) ?_, Finset.prod_pair hne]
  intro P
  rw [Finset.mem_insert, Finset.mem_singleton, ← mem_primesOver_iff, hpair, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  exact or_congr HeightOneSpectrum.ext_iff HeightOneSpectrum.ext_iff

theorem Xi_eq_of_inert (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)}
    (h' : w'.asIdeal.under (𝓞 E) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w'.asIdeal = 2)
    (hI : haveI := finiteDimensional h2; ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.under (𝓞 E) = v.asIdeal →
      Q.inertia (M ≃ₐ[E] M) = ⊥) :
    Xi ξ v = psiM ξ w' := by
  classical
  have hsing := primesOver_eq_singleton h2 h' hf (hI _ w'.isPrime h')
  rw [Xi_eq_prod h2 ξ hI ({w'} : Finset (HeightOneSpectrum (𝓞 M))) ?_, Finset.prod_singleton]
  intro P
  rw [Finset.mem_singleton, ← mem_primesOver_iff, hsing, Set.mem_singleton_iff]
  exact HeightOneSpectrum.ext_iff

end Tables

section Arch

variable {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]

omit [NumberField E] in

theorem placeOf_injective : Function.Injective (placeOf E) := by
  intro τ τ' h
  unfold placeOf at h
  rw [InfinitePlace.mk_eq_iff] at h
  have hC : Complex.ofRealHom.comp τ = Complex.ofRealHom.comp τ' := by
    rcases h with h | h
    · exact h
    · rw [← h]
      exact (ComplexEmbedding.isReal_iff.mp (isReal_compOfRealHom E τ)).symm
  ext x
  exact Complex.ofReal_injective (RingHom.congr_fun hC x)

def res (τ' : M →+* ℝ) : E →+* ℝ := τ'.comp (algebraMap E M)

omit [NumberField E] [NumberField M] in
theorem res_apply (τ' : M →+* ℝ) (x : E) : res τ' x = τ' (algebraMap E M x) := rfl

open scoped Classical in

def fibre (τ : E →+* ℝ) : Finset (M →+* ℝ) := Finset.univ.filter (fun τ' : M →+* ℝ => res τ' = τ)

omit [NumberField E] in
theorem mem_fibre {τ : E →+* ℝ} {τ' : M →+* ℝ} : τ' ∈ fibre τ ↔ res τ' = τ := by
  classical
  unfold fibre
  rw [Finset.mem_filter]
  simp

def phiOf (h2 : Module.finrank E M = 2) (τ : E →+* ℝ) : M →+* ℂ := by
  haveI := finiteDimensional h2
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  exact (IsAlgClosed.lift (R := E) (M := ℂ) (S := M)).toRingHom

theorem phiOf_algebraMap (h2 : Module.finrank E M = 2) (τ : E →+* ℝ) (x : E) :
    phiOf h2 τ (algebraMap E M x) = τ x := by
  haveI := finiteDimensional h2
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  exact (IsAlgClosed.lift (R := E) (M := ℂ) (S := M)).commutes x

theorem phiOf_comp_algebraMap (h2 : Module.finrank E M = 2) (τ : E →+* ℝ) :
    (phiOf h2 τ).comp (algebraMap E M) = Complex.ofRealHom.comp τ :=
  RingHom.ext (phiOf_algebraMap h2 τ)

def sigma0 (h2 : Module.finrank E M = 2) : M ≃ₐ[E] M := Classical.choose (exists_ne_one h2)

theorem sigma0_ne_one (h2 : Module.finrank E M = 2) : sigma0 h2 ≠ 1 :=
  Classical.choose_spec (exists_ne_one h2)

open scoped Classical in

def cOf (h2 : Module.finrank E M = 2) (τ : E →+* ℝ) : M ≃ₐ[E] M :=
  if ComplexEmbedding.IsReal (phiOf h2 τ) then 1 else sigma0 h2

theorem isConj_cOf (h2 : Module.finrank E M = 2) (τ : E →+* ℝ) :
    ComplexEmbedding.IsConj (phiOf h2 τ) (cOf h2 τ) := by
  classical
  haveI := finiteDimensional h2
  haveI := isGalois h2
  unfold cOf
  by_cases hr : ComplexEmbedding.IsReal (phiOf h2 τ)
  · rw [if_pos hr]
    exact ComplexEmbedding.isConj_one_iff.mpr hr
  · rw [if_neg hr]
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := E) (phiOf h2 τ)
      (ComplexEmbedding.conjugate (phiOf h2 τ)) (by
        ext x
        simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq,
          phiOf_algebraMap, Complex.conj_ofReal])
    have hconj : ComplexEmbedding.IsConj (phiOf h2 τ) σ.symm := hσ.symm
    have hne : σ.symm ≠ 1 := (ComplexEmbedding.isConj_ne_one_iff hconj).mpr hr
    rcases eq_one_or_eq h2 (sigma0_ne_one h2) σ.symm with h | h
    · exact absurd h hne
    · rw [← h]; exact hconj

theorem coe_theta_cOf_of_isReal (h2 : Module.finrank E M = 2) {τ : E →+* ℝ}
    (hr : ComplexEmbedding.IsReal (phiOf h2 τ)) : ((theta h2 (cOf h2 τ) : ℂˣ) : ℂ) = 1 := by
  classical
  unfold cOf
  rw [if_pos hr, map_one, Units.val_one]

theorem coe_theta_cOf_of_not_isReal (h2 : Module.finrank E M = 2) {τ : E →+* ℝ}
    (hr : ¬ ComplexEmbedding.IsReal (phiOf h2 τ)) : ((theta h2 (cOf h2 τ) : ℂˣ) : ℂ) = -1 := by
  classical
  unfold cOf
  rw [if_neg hr]
  exact coe_theta_of_ne_one h2 (sigma0_ne_one h2)

omit [NumberField E] [NumberField M] in

theorem ofRealHom_comp_eq_iff {τ' : M →+* ℝ} {φ : M →+* ℂ} (hφ : ComplexEmbedding.IsReal φ) :
    Complex.ofRealHom.comp τ' = φ ↔ τ' = hφ.embedding := by
  constructor
  · intro h
    ext x
    apply Complex.ofReal_injective
    rw [ComplexEmbedding.IsReal.coe_embedding_apply hφ x, ← h]
    rfl
  · rintro rfl
    ext x
    exact ComplexEmbedding.IsReal.coe_embedding_apply hφ x

theorem exists_eq_phiOf_comp (h2 : Module.finrank E M = 2) {τ : E →+* ℝ} {φ' : M →+* ℂ}
    (hφ' : φ'.comp (algebraMap E M) = Complex.ofRealHom.comp τ) :
    haveI := finiteDimensional h2
    ∃ g : M ≃ₐ[E] M, φ' = (phiOf h2 τ).comp (g : M →+* M) := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := E) φ' (phiOf h2 τ)
    (by rw [hφ', phiOf_comp_algebraMap])
  refine ⟨g, ?_⟩
  ext x
  have h1 : φ' (g.symm (g x)) = phiOf h2 τ (g x) := RingHom.congr_fun hg (g x)
  rw [AlgEquiv.symm_apply_apply] at h1
  rw [RingHom.comp_apply]
  exact h1

theorem fibre_eq_empty (h2 : Module.finrank E M = 2) {τ : E →+* ℝ}
    (hr : ¬ ComplexEmbedding.IsReal (phiOf h2 τ)) : fibre (M := M) τ = ∅ := by
  haveI := finiteDimensional h2
  rw [Finset.eq_empty_iff_forall_notMem]
  intro τ' hτ'
  rw [mem_fibre] at hτ'
  obtain ⟨g, hg⟩ := exists_eq_phiOf_comp h2 (τ := τ) (φ' := Complex.ofRealHom.comp τ')
    (by rw [RingHom.comp_assoc]; exact congrArg _ hτ')
  apply hr
  have hreal : ComplexEmbedding.IsReal ((phiOf h2 τ).comp (g : M →+* M)) := by
    rw [← hg]; exact isReal_compOfRealHom M τ'
  exact (ComplexEmbedding.isReal_comp_iff (f := (g : M ≃+* M))).mp hreal

open scoped Classical in

theorem fibre_eq_pair (h2 : Module.finrank E M = 2) {τ : E →+* ℝ}
    (hr : ComplexEmbedding.IsReal (phiOf h2 τ)) :
    ∃ τ₁ τ₂ : M →+* ℝ, τ₁ ≠ τ₂ ∧ fibre (M := M) τ = {τ₁, τ₂} ∧
      placeOf M τ₁ ≠ placeOf M τ₂ ∧
      (placeOf M τ₁).comap (algebraMap E M) = (placeOf M τ₂).comap (algebraMap E M) := by
  classical
  haveI := finiteDimensional h2
  set φ := phiOf h2 τ with hφ
  have hr2 : ComplexEmbedding.IsReal (φ.comp ((sigma0 h2 : M ≃ₐ[E] M) : M →+* M)) :=
    (ComplexEmbedding.isReal_comp_iff (f := ((sigma0 h2 : M ≃ₐ[E] M) : M ≃+* M))).mpr hr
  refine ⟨hr.embedding, hr2.embedding, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    apply sigma0_ne_one h2
    ext x
    have h1 := ComplexEmbedding.IsReal.coe_embedding_apply hr x
    have h2' := ComplexEmbedding.IsReal.coe_embedding_apply hr2 x
    rw [h] at h1
    rw [h1] at h2'
    simp only [RingHom.coe_comp, Function.comp_apply] at h2'
    exact (φ.injective h2'.symm)
  ·
    ext τ'
    rw [mem_fibre, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hτ'
      obtain ⟨g, hg⟩ := exists_eq_phiOf_comp h2 (τ := τ) (φ' := Complex.ofRealHom.comp τ')
        (by rw [RingHom.comp_assoc]; exact congrArg _ hτ')
      rcases eq_one_or_eq h2 (sigma0_ne_one h2) g with h1 | h1
      · left
        rw [h1] at hg
        refine (ofRealHom_comp_eq_iff hr).mp ?_
        rw [hg]; ext x; rfl
      · right
        rw [h1] at hg
        exact (ofRealHom_comp_eq_iff hr2).mp hg
    · rintro (rfl | rfl)
      · ext x
        apply Complex.ofReal_injective
        rw [res_apply, ← Complex.ofRealHom_eq_coe, ← Complex.ofRealHom_eq_coe]
        show (hr.embedding (algebraMap E M x) : ℂ) = ((τ x : ℝ) : ℂ)
        rw [ComplexEmbedding.IsReal.coe_embedding_apply hr, hφ, phiOf_algebraMap]
      · ext x
        apply Complex.ofReal_injective
        show (hr2.embedding (algebraMap E M x) : ℂ) = ((τ x : ℝ) : ℂ)
        rw [ComplexEmbedding.IsReal.coe_embedding_apply hr2, RingHom.comp_apply]
        show φ ((sigma0 h2) (algebraMap E M x)) = _
        rw [AlgEquiv.commutes, hφ, phiOf_algebraMap]
  ·
    intro h
    have := placeOf_injective h
    apply sigma0_ne_one h2
    ext x
    have h1 := ComplexEmbedding.IsReal.coe_embedding_apply hr x
    have h2' := ComplexEmbedding.IsReal.coe_embedding_apply hr2 x
    rw [this] at h1
    rw [h1] at h2'
    simp only [RingHom.coe_comp, Function.comp_apply] at h2'
    exact (φ.injective h2'.symm)
  ·
    unfold placeOf
    rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk]
    congr 1
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [Complex.ofRealHom_eq_coe, Complex.ofRealHom_eq_coe, ComplexEmbedding.IsReal.coe_embedding_apply hr,
      ComplexEmbedding.IsReal.coe_embedding_apply hr2, RingHom.comp_apply]
    show φ (algebraMap E M x) = φ ((sigma0 h2) (algebraMap E M x))
    rw [AlgEquiv.commutes]

theorem prod_fibre_mul_theta (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (τ : E →+* ℝ) :
    (((∏ τ' ∈ fibre (M := M) τ, (archLocalChar ξ (placeOf M τ') (-1) : ℂˣ)) * theta h2 (cOf h2 τ) :
        ℂˣ) : ℂ) = -1 := by
  classical
  by_cases hr : ComplexEmbedding.IsReal (phiOf h2 τ)
  · obtain ⟨τ₁, τ₂, hne, hfib, hpl, hcomap⟩ := fibre_eq_pair h2 hr
    rw [Units.val_mul, coe_theta_cOf_of_isReal h2 hr, mul_one, hfib, Finset.prod_pair hne, Units.val_mul]
    exact hsign _ _ hpl (isReal_placeOf M τ₁) (isReal_placeOf M τ₂) hcomap
  · rw [Units.val_mul, coe_theta_cOf_of_not_isReal h2 hr, fibre_eq_empty h2 hr, Finset.prod_empty,
      Units.val_one, one_mul]

theorem prod_filter_eq_prod_fibre (a : E) (s : (M →+* ℝ) → ℂˣ) :
    ∏ τ' ∈ Finset.univ.filter (fun τ' : M →+* ℝ => τ' (algebraMap E M a) < 0), s τ' =
      ∏ τ ∈ Finset.univ.filter (fun τ : E →+* ℝ => τ a < 0), ∏ τ' ∈ fibre (M := M) τ, s τ' := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (g := res (E := E) (M := M))
    (t := Finset.univ.filter (fun τ : E →+* ℝ => τ a < 0)) (fun τ' hτ' => by
      rw [Finset.mem_filter] at hτ' ⊢
      exact ⟨Finset.mem_univ _, hτ'.2⟩)]
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Finset.mem_filter] at hτ
  congr 1
  ext τ'
  rw [Finset.mem_filter, Finset.mem_filter, mem_fibre]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨Finset.mem_univ _, ?_⟩, h⟩
    rw [← res_apply, h]
    exact hτ.2

end Arch

section ArchComp

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {E : Type} [Field E] [NumberField E]

theorem archCentralUnit_fst_of_ne {v₀ v : InfinitePlace E} (hv : v ≠ v₀) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit E v₀ a : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).1 v = 1 := by
  classical
  show Function.update (1 : InfiniteAdeleRing E) v₀ (a : v₀.Completion) v = 1
  rw [Function.update_of_ne hv]
  rfl

theorem apply_archCentralUnit_eq_one_of_pos (ω : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hfin : IsOfFinOrder ω)
    (τ : E →+* ℝ) (y : ((placeOf E τ).Completion)ˣ)
    (hy : 0 < ringEquivRealOfIsReal (isReal_placeOf E τ) (y : (placeOf E τ).Completion)) :
    ω (archCentralUnit E (placeOf E τ) y) = 1 := by
  refine HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign E ω hfin _ (archCentralUnit_snd _ _) ?_
  intro τ'
  unfold archSign archRealProjTau
  by_cases h : τ' = τ
  · subst h
    rw [archCentralUnit_fst_self]
    exact hy
  · rw [archCentralUnit_fst_of_ne (fun h' => h (placeOf_injective (E := E) h')), map_one]
    exact one_pos

theorem apply_archCentralUnit_eq_one_of_isComplex (ω : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hfin : IsOfFinOrder ω) {w : InfinitePlace E} (hw : w.IsComplex) (y : (w.Completion)ˣ) :
    ω (archCentralUnit E w y) = 1 := by
  refine HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign E ω hfin _ (archCentralUnit_snd _ _) ?_
  intro τ'
  unfold archSign archRealProjTau
  have hne : placeOf E τ' ≠ w := fun h => by
    have := isReal_placeOf E τ'
    rw [h] at this
    exact (not_isReal_iff_isComplex.mpr hw) this
  rw [archCentralUnit_fst_of_ne hne, map_one]
  exact one_pos

theorem isArchCompAt_placeOf (ω : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hfin : IsOfFinOrder ω)
    (τ : E →+* ℝ) (hneg : ((archLocalChar ω (placeOf E τ) (-1) : ℂˣ) : ℂ) = -1) :
    IsArchCompAt E ω (placeOf E τ) 0 1 := by
  intro x
  set r : ℝ := ringEquivRealOfIsReal (isReal_placeOf E τ) (x : (placeOf E τ).Completion) with hr
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact (map_ne_zero _).mpr x.ne_zero
  have he : extensionEmbedding (placeOf E τ) (x : (placeOf E τ).Completion) = (r : ℂ) := by
    rw [hr, ringEquivRealOfIsReal_apply, extensionEmbeddingOfIsReal_apply]
  have hn : (‖(x : (placeOf E τ).Completion)‖ : ℂ) = ((|r| : ℝ) : ℂ) := by
    congr 1
    rw [← (isometry_extensionEmbedding (placeOf E τ)).norm_map_of_map_zero (map_zero _) _, he,
      Complex.norm_real, Real.norm_eq_abs]
  rw [mul_zero, Complex.cpow_zero, one_mul, zpow_one, he, hn]
  rcases hr0.lt_or_gt with hlt | hgt
  ·
    have hx : x = (-1) * (-x) := by rw [neg_one_mul, neg_neg]
    have hpos : 0 < ringEquivRealOfIsReal (isReal_placeOf E τ) (((-x : ((placeOf E τ).Completion)ˣ)) :
        (placeOf E τ).Completion) := by
      rw [Units.val_neg, map_neg, ← hr]
      exact neg_pos.mpr hlt
    rw [hx, map_mul, Units.val_mul, archLocalChar_apply ω (placeOf E τ) (-x),
      apply_archCentralUnit_eq_one_of_pos ω hfin τ _ hpos, Units.val_one, mul_one, hneg, abs_of_neg hlt,
      Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.mpr hr0)]
  · rw [archLocalChar_apply, apply_archCentralUnit_eq_one_of_pos ω hfin τ _ (by rw [← hr]; exact hgt),
      Units.val_one, abs_of_pos hgt, div_self (Complex.ofReal_ne_zero.mpr hr0)]

theorem isArchCompAt_of_isComplex (ω : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hfin : IsOfFinOrder ω)
    {w : InfinitePlace E} (hw : w.IsComplex) : IsArchCompAt E ω w 0 0 := by
  intro x
  rw [mul_zero, Complex.cpow_zero, one_mul, zpow_zero, archLocalChar_apply,
    apply_archCentralUnit_eq_one_of_isComplex ω hfin hw, Units.val_one]

omit [NumberField E] in

theorem exists_placeOf_eq {w : InfinitePlace E} (hw : w.IsReal) : ∃ τ : E →+* ℝ, placeOf E τ = w := by
  refine ⟨embedding_of_isReal hw, ?_⟩
  unfold placeOf
  have : Complex.ofRealHom.comp (embedding_of_isReal hw) = w.embedding := by
    ext x
    exact embedding_of_isReal_apply hw x
  rw [this, mk_embedding]

end ArchComp

section LocalUnits

variable {E : Type} [Field E] [NumberField E]

theorem idealMultiplicity_eq_zero_of_not_dvd {𝔣 : Ideal (𝓞 E)} (h𝔣 : 𝔣 ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ¬ v.asIdeal ∣ 𝔣) : idealMultiplicity E v 𝔣 = 0 := by
  classical
  unfold idealMultiplicity
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp h)

theorem localChar_eq_one_of_valued_eq_one {η : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 E)}
    (h𝔣 : 𝔣 ≠ ⊥) (hmod : AdmitsModulus E η 𝔣) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ 𝔣) (t : (v.adicCompletion E)ˣ) (ht : Valued.v (t : v.adicCompletion E) = 1) :
    localChar η v t = 1 := by
  classical
  rw [localChar_apply]
  apply hmod
  · rfl
  · intro w
    show Valued.v (((localUnit (𝓞 E) E v t : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) w) = 1 ∧
      Valued.v (((localUnit (𝓞 E) E v t : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) w - 1) ≤
        WithZero.exp (-(idealMultiplicity E w 𝔣 : ℤ))
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, idealMultiplicity_eq_zero_of_not_dvd h𝔣 hv]
      refine ⟨ht, ?_⟩
      simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
      calc Valued.v ((t : w.adicCompletion E) - 1)
          ≤ max (Valued.v (t : w.adicCompletion E)) (Valued.v (1 : w.adicCompletion E)) :=
            Valuation.map_sub _ _ _
        _ = 1 := by rw [ht, map_one, max_self]
    · rw [localUnit_apply_of_ne (𝓞 E) E v t hw]
      refine ⟨map_one _, ?_⟩
      rw [sub_self, map_zero]
      exact zero_le'

theorem isUnramifiedCharAt_of_not_dvd {η : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 E)}
    (h𝔣 : 𝔣 ≠ ⊥) (hmod : AdmitsModulus E η 𝔣) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ¬ v.asIdeal ∣ 𝔣) : IsUnramifiedCharAt η v := by
  intro t ht htinv
  apply localChar_eq_one_of_valued_eq_one h𝔣 hmod hv t
  have h1 : Valued.v (t : v.adicCompletion E) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ht
  have h2 : Valued.v (((t⁻¹ : (v.adicCompletion E)ˣ)) : v.adicCompletion E) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp htinv
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  have h0 : Valued.v (t : v.adicCompletion E) ≠ 0 := by
    rw [ne_eq, map_eq_zero]; exact t.ne_zero
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

end LocalUnits

end DetInducedSol

end

open scoped IsMulCommutative in
open DetInducedSol NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter Deep.NTSupply NumberField.AdelicLevel NumberField.AdelicVolume LanglandsTunnell.P2.Artin LanglandsTunnell.Converse in

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1) :
    ∃ ω : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ,
      IsAdmissibleTwist E ω ∧
      (∀ w : InfinitePlace E, w.IsReal → IsArchCompAt E ω w 0 1) ∧
      (∀ w : InfinitePlace E, w.IsComplex → IsArchCompAt E ω w 0 0) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
        IsUnramifiedCharAt ω w ∧
        (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
          ((ω (uniformizerIdele E w) : ℂˣ) : ℂ) =
            (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
        (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
          ((ω (uniformizerIdele E w) : ℂˣ) : ℂ) = -(ξ (uniformizerIdele M w') : ℂ)) := by
  classical
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI := isMulCommutative h2

  obtain ⟨𝔣₁, h𝔣₁, hunr, hrecip⟩ := NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj E M

  obtain ⟨𝔣M, h𝔣M, hmodM⟩ :=
    HeckeCharacter.exists_admitsModulus_of_continuous_of_isOfFinOrder M ξ hξ.continuous hξ.isOfFinOrder
  set 𝔣₂ : Ideal (𝓞 E) := 𝔣M.comap (algebraMap (𝓞 E) (𝓞 M)) with h𝔣₂def
  have h𝔣₂ : 𝔣₂ ≠ ⊥ := fun h => h𝔣M (Ideal.eq_bot_of_comap_eq_bot h)
  set 𝔣 : Ideal (𝓞 E) := 𝔣₁ * 𝔣₂ with h𝔣def
  have h𝔣 : 𝔣 ≠ ⊥ := fun h => by
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact h𝔣₁ h
    · exact h𝔣₂ h

  set η : HeightOneSpectrum (𝓞 E) → ℂˣ := fun v => theta h2 (artinFrob E M v) with hηdef
  set ψE : HeightOneSpectrum (𝓞 E) → ℂˣ := fun v => η v * Xi ξ v with hψEdef
  have hray : ∀ α : 𝓞 E, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol E ψE ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
        ∏ τ ∈ Finset.univ.filter (fun τ : E →+* ℝ => τ (algebraMap (𝓞 E) E α) < 0), (-1 : ℂˣ) := by
    intro α hα hα1
    have hα1₁ : α - 1 ∈ 𝔣₁ := Ideal.mul_le_left hα1
    have hα1₂ : α - 1 ∈ 𝔣₂ := Ideal.mul_le_right hα1

    have hcop : principalUnit E α hα ∈ coprimeToModulus E (⊤ : Ideal (𝓞 E)) := by
      rw [coprimeToModulus_top]; trivial
    have hA := hrecip α hα ⊤ hcop (cOf h2) hα1₁
      (fun τ => ⟨phiOf h2 τ, phiOf_algebraMap h2 τ, isConj_cOf h2 τ⟩)
    have hη : raySymbol E η ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
        ∏ τ ∈ Finset.univ.filter (fun τ : E →+* ℝ => τ (algebraMap (𝓞 E) E α) < 0),
          theta h2 (cOf h2 τ) := by
      have hθ := congrArg (theta h2) hA
      rw [map_artinSymbol, map_prod] at hθ
      rw [← hθ, ← principalUnit_val E α hα]

    have hαM : algebraMap (𝓞 E) (𝓞 M) α ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_ringOfIntegers_injective E M)).mpr hα
    have hαM1 : algebraMap (𝓞 E) (𝓞 M) α - 1 ∈ 𝔣M := by
      have := Ideal.mem_comap.mp hα1₂
      rwa [map_sub, map_one] at this
    have hΞ : raySymbol E (Xi ξ) ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
        ∏ τ' ∈ Finset.univ.filter (fun τ' : M →+* ℝ =>
            τ' (algebraMap (𝓞 M) M (algebraMap (𝓞 E) (𝓞 M) α)) < 0),
          archLocalChar ξ (InfinitePlace.mk (Complex.ofRealHom.comp τ')) (-1) := by
      rw [raySymbol_Xi ξ (by rwa [Ne, Ideal.span_singleton_eq_bot]), extFrac_span_singleton]
      exact HeckeCharacter.raySymbol_apply_uniformizerIdele_eq_prod_archLocalChar_neg_one_of_admitsModulus
        M ξ hξ.isIdeleClassChar hξ.isOfFinOrder 𝔣M h𝔣M hmodM _ hαM hαM1
    have halg : algebraMap (𝓞 M) M (algebraMap (𝓞 E) (𝓞 M) α) = algebraMap E M (algebraMap (𝓞 E) E α) := by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [halg, prod_filter_eq_prod_fibre] at hΞ

    rw [raySymbol_mul_table, hη, hΞ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    apply Units.ext
    rw [mul_comm, Units.val_neg, Units.val_one]
    exact prod_fibre_mul_theta h2 ξ hsign τ

  obtain ⟨ω, hfo, hmod, huni, hval, harch⟩ :=
    HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
      E 𝔣 h𝔣 ψE (fun _ => -1) hray
  refine ⟨ω, ⟨hfo.isIdeleClassChar, hfo.continuous, huni⟩, ?_, ?_, ?_⟩
  ·
    intro w hw
    obtain ⟨τ, rfl⟩ := exists_placeOf_eq hw
    apply isArchCompAt_placeOf ω hfo.isOfFinOrder τ
    have hτ := harch τ
    show ((archLocalChar ω (InfinitePlace.mk (Complex.ofRealHom.comp τ)) (-1) : ℂˣ) : ℂ) = -1
    rw [hτ, Units.val_neg, Units.val_one]
  ·
    intro w hw
    exact isArchCompAt_of_isComplex ω hfo.isOfFinOrder hw
  ·
    refine ⟨(Ideal.finite_factors h𝔣).toFinset, fun w hw => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw
    have hw₁ : ¬ w.asIdeal ∣ 𝔣₁ := fun h => hw (dvd_mul_of_dvd_left h _)
    have hIw : ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.under (𝓞 E) = w.asIdeal →
        Q.inertia (M ≃ₐ[E] M) = ⊥ := hunr w hw₁
    have hωw : ((ω (uniformizerIdele E w) : ℂˣ) : ℂ) = ((η w : ℂˣ) : ℂ) * ((Xi ξ w : ℂˣ) : ℂ) := by
      rw [hval w hw, ← Units.val_mul]
    refine ⟨isUnramifiedCharAt_of_not_dvd h𝔣 hmod hw, ?_, ?_⟩
    ·
      intro w' w'' hne h' h''
      have h'₁ : w'.asIdeal.under (𝓞 E) = w.asIdeal := by rw [← HeightOneSpectrum.under_asIdeal, h']
      have h''₁ : w''.asIdeal.under (𝓞 E) = w.asIdeal := by rw [← HeightOneSpectrum.under_asIdeal, h'']
      have hcard := (primesOver_eq_pair h2 hne h'₁ h''₁ (hIw _ w'.isPrime h'₁)).2
      have hFrob : artinFrob E M w = 1 := artinFrob_eq_one_of_ncard_eq_two h2 hcard hIw
      have hηw : η w = 1 := by
        show theta h2 (artinFrob E M w) = 1
        rw [hFrob, map_one]
      rw [hωw, hηw, Xi_eq_mul_of_split h2 ξ hne h'₁ h''₁ hIw, Units.val_one, one_mul, Units.val_mul]
      rfl
    ·
      intro w' h' hf
      have h'₁ : w'.asIdeal.under (𝓞 E) = w.asIdeal := by rw [← HeightOneSpectrum.under_asIdeal, h']
      have hFrob := artinFrob_ne_one_of_inertiaDeg_eq_two h2 h'₁ hf (hIw _ w'.isPrime h'₁)
      have hηw : ((η w : ℂˣ) : ℂ) = -1 := coe_theta_of_ne_one h2 hFrob
      rw [hωw, hηw, Xi_eq_of_inert h2 ξ h'₁ hf hIw, neg_one_mul]
      rfl

end S_LanglandsTunnell_exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two (solution)
