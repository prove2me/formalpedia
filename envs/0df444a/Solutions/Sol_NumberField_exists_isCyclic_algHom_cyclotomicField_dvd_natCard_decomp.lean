-- Prove2me | solution 1 for NumberField.exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/38cbc75c-3430-5f48-87de-5156adb0dcdd

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
import Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe"
p2m_attr_erase "simp" "ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain

theorem solution
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) (hn : 0 < n) :
    ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsCyclic (F' ≃ₐ[E] F')),

      Nonempty (F' →ₐ[E] CyclotomicField m E) ∧

      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧

      n ∣ Nat.card (F' ≃ₐ[E] F') ∧

      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) := by
  classical

  suffices H : ∀ k : ℕ, 0 < k → ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F')
      (_ : IsGalois E F') (_ : IsCyclic (F' ≃ₐ[E] F')),
      Nonempty (F' →ₐ[E] CyclotomicField m E) ∧
      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧
      k ∣ Nat.card (F' ≃ₐ[E] F') ∧
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) ∧
      (k = 1 ∨ ∀ q : ℕ, q.Prime → q ∣ Nat.card (F' ≃ₐ[E] F') → q ∣ k) by
    obtain ⟨m, hm, F', iF, iN, iA, iG, iC, h1, h2, h3, h4, -⟩ := H n hn
    exact ⟨m, hm, F', iF, iN, iA, iG, iC, h1, h2, h3, h4⟩
  intro k
  induction k using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | prime_pow p a hp =>
    intro _
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := NeZero.of_pos hp.pos

    obtain ⟨c, F', iF, iN, iA, iG, iC, h1, h2, h3, h4, h5⟩ :=
      NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp E T p a
    refine ⟨p ^ c, inferInstance, F', iF, iN, iA, iG, iC, h1, h2, h3, h4, ?_⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact Or.inl (pow_zero p)
    · refine Or.inr fun q hq hqd => ?_
      obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := p) (G := F' ≃ₐ[E] F')).1 h5
      rw [hb] at hqd
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)
      subst hqp
      exact dvd_pow_self q ha.ne'
  | coprime a b ha hb hab iha ihb =>
    intro _
    obtain ⟨m₁, hm₁, F₁, iF₁, iN₁, iA₁, iG₁, iC₁, c₁, i₁, d₁, l₁, s₁⟩ := iha (lt_trans Nat.one_pos ha)
    obtain ⟨m₂, hm₂, F₂, iF₂, iN₂, iA₂, iG₂, iC₂, c₂, i₂, d₂, l₂, s₂⟩ := ihb (lt_trans Nat.one_pos hb)
    have s₁' := s₁.resolve_left ha.ne'
    have s₂' := s₂.resolve_left hb.ne'

    have hcop : Nat.Coprime (Nat.card (F₁ ≃ₐ[E] F₁)) (Nat.card (F₂ ≃ₐ[E] F₂)) :=
      Nat.coprime_of_dvd fun q hq hq₁ hq₂ => hq.ne_one (Nat.eq_one_of_dvd_coprimes hab (s₁' q hq hq₁) (s₂' q hq hq₂))

    obtain ⟨m, hm, F', iF, iN, iA, iG, iC, c, i, d, l, o⟩ :=
      NumberField.exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime E T
        a m₁ F₁ c₁ i₁ d₁ l₁ b m₂ F₂ c₂ i₂ d₂ l₂ hcop
    refine ⟨m, hm, F', iF, iN, iA, iG, iC, c, i, d, l, Or.inr fun q hq hqd => ?_⟩
    rcases (Nat.Prime.dvd_mul hq).1 (dvd_trans hqd o) with h | h
    · exact dvd_mul_of_dvd_left (s₁' q hq h) b
    · exact dvd_mul_of_dvd_right (s₂' q hq h) a

end S_NumberField_exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp
end P2MW
export P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp (solution)
