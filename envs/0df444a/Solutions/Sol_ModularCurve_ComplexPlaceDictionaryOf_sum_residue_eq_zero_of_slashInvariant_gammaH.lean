-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionaryOf.sum_residue_eq_zero_of_slashInvariant_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/20aba2bd-40a5-5e21-95d7-c39cd2071bc9

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH
import Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer_gammaH
import Theorems.Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.jqNModC_one AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "ComplexPlaceDictionaryOf laurentBaseChange Gamma1_le_GammaH xHFunctionField ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH"
namespace ComplexPlaceDictionaryOf
p2m_export "ModularCurve.ComplexPlaceDictionaryOf" "pt_smul_of_mem ramification ramification_pos pt pt_eq_pt_iff_gammaH two_mul_ramification_eq_card_stabilizer_gammaH"
namespace SumResH
p2m_open "ModularCurve.ComplexPlaceDictionaryOf ModularCurve"

theorem mem_sup_zpowers_neg_one_iff (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) :
    γ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ γ ∈ Γ ∨ -γ ∈ Γ := by
  haveI : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc : g * (-1 : SL(2, ℤ)) ^ k * g⁻¹ = (-1) ^ k := by
      rw [((Commute.neg_one_right g).zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hz : ∀ a : SL(2, ℤ), a ∈ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ a = 1 ∨ a = -1 := by
    intro a
    constructor
    · intro ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rcases Int.even_or_odd k with hk | hk
      · left; rw [hk.neg_one_zpow]
      · right; rw [hk.neg_one_zpow]
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact Subgroup.mem_zpowers _
  constructor
  · intro h
    have h' : γ ∈ ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)) := h
    rw [Subgroup.mul_normal] at h'
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp h'
    rcases (hz b).mp hb with rfl | rfl
    · left; simpa using ha
    · right; simpa using ha
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : γ = -γ * (-1) := by simp
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem slash_two_neg (ω : ℍ → ℂ) (γ : SL(2, ℤ)) : ω ∣[(2 : ℤ)] (-γ) = ω ∣[(2 : ℤ)] γ := by
  funext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul]
  congr 1
  have hden : denom ((-γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.denom_apply, ModularGroup.denom_apply]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    push_cast
    ring
  rw [hden, Even.neg_zpow (by decide : Even (-2 : ℤ))]

end ModularCurve.ComplexPlaceDictionaryOf.SumResH

open ModularCurve.ComplexPlaceDictionaryOf.SumResH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →₀ ℂ)
    (hΓ : ∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hsupp : ∀ P ∈ r.support, ∃ τ : ℍ, D.pt τ = P)
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z) :
    r.sum (fun _ a => a) = 0 := by
  classical
  set Γ : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) with hΓdef
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
      (CongruenceSubgroup.Gamma1_is_congruence M)).finiteIndex
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (K := Γ) (H := CohCarrier.GammaH M H) le_sup_left

  have hΓ' : ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω := by
    intro γ hγ
    rcases (mem_sup_zpowers_neg_one_iff _ γ).mp hγ with h | h
    · exact hΓ γ h
    · rw [← neg_neg γ, slash_two_neg]
      exact hΓ (-γ) h
  have hpt : ∀ γ ∈ Γ, ∀ τ : ℍ, D.pt (γ • τ) = D.pt τ := by
    intro γ hγ τ
    rcases (mem_sup_zpowers_neg_one_iff _ γ).mp hγ with h | h
    · exact D.pt_smul_of_mem h τ
    · have hγ' : γ = (-1 : SL(2, ℤ)) * (-γ) := by simp
      rw [hγ', mul_smul, ModularGroup.SL_neg_smul, one_smul]
      exact D.pt_smul_of_mem h τ

  choose! lift hlift using hsupp
  set c : ℍ → ℂ := fun τ => (D.ramification τ : ℂ) * r (D.pt τ) with hc
  set S : Finset ℍ := r.support.image lift with hS_def
  have hloc' : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = c τ / (z - τ) + g z := by
    intro τ
    obtain ⟨g, hg, hω⟩ := hloc τ
    exact ⟨g, hg, hω⟩
  have hS : ∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ := by
    intro τ hτ
    have hr : r (D.pt τ) ≠ 0 := by
      intro h
      exact hτ (by simp [hc, h])
    have hmem : D.pt τ ∈ r.support := Finsupp.mem_support_iff.2 hr
    refine ⟨lift (D.pt τ), Finset.mem_image_of_mem _ hmem, ?_⟩
    have hptl : D.pt (lift (D.pt τ)) = D.pt τ := hlift _ hmem
    obtain ⟨γ, hγ, hγe⟩ :=
      (ModularCurve.ComplexPlaceDictionaryOf.pt_eq_pt_iff_gammaH M H D (lift (D.pt τ)) τ).1 hptl
    exact ⟨γ, Subgroup.mem_sup_left hγ, hγe⟩
  have hinj : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ' := by
    intro σ hσ σ' hσ' γ hγ hγσ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 hσ'
    have h1 : D.pt (γ • lift P) = D.pt (lift P) := hpt γ hγ (lift P)
    rw [hγσ, hlift P' hP', hlift P hP] at h1
    rw [h1]
  have key := UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
    Γ ω c S hΓ' hcusp hloc' hS hinj
  have hlift_inj : Set.InjOn lift (r.support : Set _) := by
    intro P hP P' hP' h
    have := congrArg D.pt h
    rwa [hlift P hP, hlift P' hP'] at this
  rw [hS_def, Finset.sum_image hlift_inj] at key
  have hterm : ∀ P ∈ r.support,
      c (lift P) / (Nat.card (MulAction.stabilizer Γ (lift P)) : ℂ) = r P / 2 := by
    intro P hP
    have hcard := ModularCurve.ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer_gammaH
      M H D (lift P)
    have he : (D.ramification (lift P) : ℂ) ≠ 0 := by
      exact_mod_cast (D.ramification_pos (lift P)).ne'
    rw [hΓdef, ← hcard, hc]
    simp only [hlift P hP]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div] at key
  have hsum : ∑ P ∈ r.support, r P = 0 := by
    rcases div_eq_zero_iff.1 key with h | h
    · exact h
    · norm_num at h
  simpa [Finsupp.sum] using hsum

end S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH (solution)
