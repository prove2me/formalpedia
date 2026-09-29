-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ca4514c6-c8c0-578c-8f3b-d6997fc4a427

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Theorems.Thm_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Pointwise

namespace FamiliesH

section Generic
variable {κ F : Type*} [Field κ] [Field F] [Algebra κ F]

theorem ne_zero_of_ord_pos (v : Place κ F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

theorem sep_ord_pos (v : Place κ F) (g : F) {c₁ c₂ : κ}
    (h₁ : 0 < v.ord (g - algebraMap κ F c₁)) (h₂ : 0 < v.ord (g - algebraMap κ F c₂)) : c₁ = c₂ := by
  by_contra hne
  have hsub : (g - algebraMap κ F c₂) - (g - algebraMap κ F c₁) = algebraMap κ F (c₁ - c₂) := by
    rw [map_sub]; ring
  have hv₁ : v.adicValuation (g - algebraMap κ F c₁) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₁), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv₂ : v.adicValuation (g - algebraMap κ F c₂) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₂), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : v.adicValuation (algebraMap κ F (c₁ - c₂)) < 1 := by
    rw [← hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv₂ hv₁)
  have hord0 : v.ord (algebraMap κ F (c₁ - c₂)) = 0 := ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)
  rw [v.adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (sub_ne_zero.mpr hne)), hord0] at hval
  simp at hval

open Classical in
noncomputable def valOf (g : F) (t : Place κ F) : κ :=
  if h : ∃ c, 0 < t.ord (g - algebraMap κ F c) then h.choose else 0

theorem valOf_eq {g : F} {t : Place κ F} {c : κ} (h : 0 < t.ord (g - algebraMap κ F c)) : valOf g t = c := by
  classical
  have hex : ∃ c', 0 < t.ord (g - algebraMap κ F c') := ⟨c, h⟩
  unfold valOf
  rw [dif_pos hex]
  exact sep_ord_pos t g hex.choose_spec h

theorem ord_sub_pos_of_hasValue' (v : Place κ F) {g : F} {a : κ} (h : v.HasValue g a) (hne : g - algebraMap κ F a ≠ 0) :
    0 < v.ord (g - algebraMap κ F a) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap κ F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : (⟨g - algebraMap κ F a, hmem⟩ : v.toValuationSubring)
        = ⟨g, hg⟩ - ⟨algebraMap κ F a, v.algebraMap_mem' a⟩ := rfl
    rw [this, map_sub, hres, sub_eq_zero]
    rfl
  have h0 := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hpos | h0
  · exact hpos
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hne hπ
    rw [← h0, zpow_zero, mul_one] at hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have : (⟨g - algebraMap κ F a, hmem⟩ : v.toValuationSubring) = (u : v.toValuationSubring) := Subtype.ext hu
    rw [this]; exact Units.isUnit u

end Generic

theorem exists_injective_of_infinite {α : Type*} {S : Set α} (hS : S.Infinite) (B : Finset α) (m : ℕ) :
    ∃ e : Fin m → α, Function.Injective e ∧ ∀ i, e i ∈ S ∧ e i ∉ B := by
  classical
  have hS' : (S \ (↑B : Set α)).Infinite := hS.diff B.finite_toSet
  obtain ⟨t, ht, hcard⟩ := hS'.exists_subset_card_eq m
  have e0 : Fin m ≃ ↥t := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard])).symm
  refine ⟨fun i => (e0 i : α), ?_, fun i => ?_⟩
  · intro i j h
    exact e0.injective (Subtype.ext h)
  · have hmem : ((e0 i : α)) ∈ S \ (↑B : Set α) := ht (e0 i).2
    exact ⟨hmem.1, fun hb => hmem.2 (Finset.mem_coe.mpr hb)⟩

end FamiliesH

namespace FamiliesH

theorem restrictAlong_smul_of_forall_map_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (g : SemilinearAut K F) (g' : SemilinearAut K F')
    (hcomm : ∀ u : F, φ (g • u) = g' • φ u) (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  have hcomm' : ∀ u : F, φ (g⁻¹ • u) = g'⁻¹ • φ u := fun u => by
    have := hcomm (g⁻¹ • u)
    rw [smul_inv_smul] at this
    rw [this, inv_smul_smul]
  apply Place.ext
  ext x
  show φ x ∈ (g' • w).toValuationSubring ↔ x ∈ g • (w.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  show g'⁻¹ • φ x ∈ w.toValuationSubring ↔ φ (g⁻¹ • x) ∈ w.toValuationSubring
  rw [hcomm']

end FamiliesH

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem FamiliesH.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceFst α hα W ∧
      Psp.reduceSnd β hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceSnd β hβ δ W := by
  intro σ hσ W

  set G := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ with hG
  set G' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ with hG'
  have hαeq : ∀ u, α (G' • u) = G • α u := fun u => by
    apply Subtype.ext
    rw [hα_coe, hG', coe_arithmeticGalois_smul, hG, coe_arithmeticGalois_smul, hα_coe]
  have hβapp : ∀ u, β u = θ (α u) := fun u => by rw [hβθ]; rfl
  have hβeq : ∀ u, β (G' • u) = G • β u := fun u => by
    rw [hβapp, hβapp, hαeq, hG, hθgal]
  refine ⟨?_, ?_⟩
  · show Psp.sp ((G • W).restrictAlong α hα) = Psp.sp (W.restrictAlong α hα)
    rw [FamiliesH.restrictAlong_smul_of_forall_map_smul α hα G' G hαeq W, hG']
    exact Psp.d6_inertia σ hσ _
  · show δ (Psp.sp ((G • W).restrictAlong β hβ)) = δ (Psp.sp (W.restrictAlong β hβ))
    rw [FamiliesH.restrictAlong_smul_of_forall_map_smul β hβ G' G hβeq W, hG']
    rw [Psp.d6_inertia σ hσ]

open FamiliesH

open Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    :
    ∃ Bad : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ Bad →
        (∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          Psp.IsStrictFst α β hα hβ δ W ∧ Psp.reduceFst α hα W = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W = W) ∧
        (∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          Psp.IsStrictSnd α β hα hβ δ W ∧ Psp.reduceSnd β hβ δ W = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W = W) := by
  classical

  let κ := ResidueField ↥A
  let Γ' := JHNeronObjectAtP.ΓN p M H hpM
  let Fb := JHNeronObjectAtP.Fbar p M H hpM κ
  let G := fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ
  let r₁ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Place κ Fb := Psp.reduceFst α hα
  let r₂ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Place κ Fb := Psp.reduceSnd β hβ δ
  have hT' : ModularGroup.T ∈ Γ' := translation_mem_GammaH (M / p) (infSubgroup p M H hpM)

  haveI hICF : IsCurveOver κ Fb :=
    (isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A Γ' hT').1
  obtain ⟨jb, hjb, hjbtr, hjbfd, -⟩ := exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A Γ' hT'
  haveI := hjbfd
  haveI hjbalg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin κ ({jb} : Set Fb)) Fb := Algebra.IsAlgebraic.of_finite _ _
  have hjmem : jqModC κ ∈ qExpFunctionFieldC κ Γ' := hjb ▸ jb.2
  have hjbeq : (⟨jqModC κ, hjmem⟩ : Fb) = jb := Subtype.ext hjb.symm
  have hjbsep : Algebra.IsSeparable ↥(IntermediateField.adjoin κ ({jb} : Set Fb)) Fb := by
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin κ ({(⟨jqModC κ, hjmem⟩ : Fb)} : Set Fb)) Fb := by
      rw [hjbeq]; exact hjbalg
    have h := isSeparable_adjoin_jqModC_of_isAlgebraic κ (qExpFunctionFieldC κ Γ') hjmem
    rw [hjbeq] at h
    exact h
  obtain ⟨C, hC⟩ := AlgebraicCurve.Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos jb hjbtr hjbfd hjbsep
  have hjbc : ∀ c : κ, jb - algebraMap κ Fb c ≠ 0 := by
    intro c h
    apply hjbtr
    rw [sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap c
  have hjb0 : (jb : Fb) ≠ 0 := by simpa using hjbc 0

  have hzero : ∀ c : κ, ∃ v : Place κ Fb, 0 < v.ord (jb - algebraMap κ Fb c) := by
    intro a
    obtain ⟨xp, hxptr, hxpfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ' hT'
    obtain ⟨w₀, -⟩ := @AlgebraicCurve.Place.exists_ord_neg_of_transcendental (AlgebraicClosure ℚ) _ _ _ _ _ xp hxptr hxpfd
    let v₀ : Place κ Fb := Psp.sp w₀
    have hCB : ConstantsAreBase κ Fb := constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
    have hpole : ∃ v : Place κ Fb, v.ord (jb : Fb) < 0 := by
      by_contra hno
      push Not at hno
      have hmem : (jb : Fb) ∈ LSpace (0 : Divisor κ Fb) := by
        rw [mem_lSpace_iff_ord]
        refine Or.inr fun v => ?_
        rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
        exact hno v
      rw [show LSpace (0 : Divisor κ Fb) = _ from hCB] at hmem
      obtain ⟨c, hc⟩ := hmem
      apply hjbc c
      rw [← hc, Algebra.linearMap_apply, sub_self]
    obtain ⟨v₁, hv₁⟩ := hpole
    have hne := hjbc a
    have hxa : v₁.ord (jb - algebraMap κ Fb a) < 0 := by
      have hnotmem : (jb : Fb) ∉ v₁.toValuationSubring := fun hmem => not_lt.mpr (v₁.ord_nonneg_of_mem hmem) hv₁
      by_contra hge
      push Not at hge
      have hmem := v₁.mem_of_ord_nonneg hne hge
      have := add_mem hmem (v₁.algebraMap_mem' a)
      rw [sub_add_cancel] at this
      exact hnotmem this
    haveI hPDb : HasPrincipalDivisors κ Fb := IsCurveOver.hasPrincipalDivisors
    obtain ⟨D, hD, hdeg⟩ := hPDb.exists_divisor (jb - algebraMap κ Fb a) hne
    by_contra hall
    push Not at hall
    have hall' : ∀ v, 0 ≤ (-D) v := fun v => by rw [Finsupp.neg_apply, neg_nonneg, hD v]; exact hall v
    have hv₀ : 0 < (-D) v₁ := by rw [Finsupp.neg_apply, neg_pos, hD v₁]; exact hxa
    have hmem : v₁ ∈ (-D).support := Finsupp.mem_support_iff.mpr hv₀.ne'
    have hdegsum : Divisor.degree (-D) = ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) := by
      conv_lhs => rw [← Finsupp.sum_single (-D), Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v ((-D) v)
    have hdegpos : 0 < Divisor.degree (-D) := by
      rw [hdegsum]
      calc (0 : ℤ) < (-D) v₁ * (v₁.deg : ℤ) := by
            rw [IsCurveOver.deg_eq_one_of_isAlgClosed v₁, Nat.cast_one, mul_one]; exact hv₀
        _ ≤ ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) :=
            Finset.single_le_sum (fun v _ => mul_nonneg (hall' v) (Int.natCast_nonneg _)) hmem
    rw [map_neg, hdeg, neg_zero] at hdegpos
    exact lt_irrefl 0 hdegpos

  haveI hPDb' : HasPrincipalDivisors κ Fb := IsCurveOver.hasPrincipalDivisors
  have hsurjb : ∀ v : Place κ Fb, Function.Surjective (algebraMap κ v.ResidueField) :=
    (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2 κ).2.2
  obtain ⟨Djb, hDjb, -⟩ := hPDb'.exists_divisor (jb : Fb) hjb0
  choose Dc hDc _hDcdeg using fun c : κ => hPDb'.exists_divisor (jb - algebraMap κ Fb c) (hjbc c)
  let BadCrit : Finset (Place κ Fb) := C.biUnion fun c => (Dc c).support

  have hFixfin := ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift p M H hpM hpM2 A hA pb hpb δ hδ
  let BadFix : Finset κ := hFixfin.toFinset.image (valOf jb)

  have hOS := ModularCurve.JHPlaceSpecialization.ProlongationDatum.oneSidedDivisorLaw_and_oneSidedCuspLaw_of_isModel_of_unit
    p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hUnit
  have hK2 := FamiliesH.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
    p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ

  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
    obtain ⟨x, hxtr, hxfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (translation_mem_GammaH M H)
    exact @AlgebraicCurve.hasPrincipalDivisors_of_transcendental (AlgebraicClosure ℚ) _ _ _ _ _ x hxtr hxfd

  have hjq : jq = jqModC ℚ := by
    rw [← coeffEmb_jq ℚ]
    ext n; simp [coeffEmb]
  have hmemM : jq ∈ xHFunctionField M H := by
    rw [hjq]; exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)
  have hJmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [coeffMap_jqModC, ← coeffEmb_jq]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmemM
  let Jα : ↥(xHFunctionFieldBar M H) := ⟨coeffMap A.subtype (jqModC ↥A), hJmem⟩
  have hJαfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • Jα = Jα := by
    intro σ _
    apply Subtype.ext
    show ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Jα : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [coe_arithmeticGalois_smul]
    show coeffMap _ (coeffMap A.subtype (jqModC ↥A)) = coeffMap A.subtype (jqModC ↥A)
    rw [coeffMap_jqModC, coeffMap_jqModC]
  obtain ⟨hJαint, hJαres'⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hJmem
  have hJαres : (Rpd.R₁.residue ⟨Jα, hJαint⟩ : Fb) = jb := by
    apply Subtype.ext
    rw [hJαres', coeffMap_jqModC, hjb]
  let Jθ : ↥(xHFunctionFieldBar M H) := θ.symm Jα
  have hJθint : Jθ ∈ Rpd.R₂.integers := by
    rw [Rpd.mem_integers₂_iff]
    show θ (θ.symm Jα) ∈ _
    rw [AlgEquiv.apply_symm_apply]; exact hJαint
  have hJθres : (Rpd.R₂.residue ⟨Jθ, hJθint⟩ : Fb) = jb := by
    rw [Rpd.residue₂_eq]
    have e : (⟨θ Jθ, (Rpd.mem_integers₂_iff Jθ).mp hJθint⟩ : ↥Rpd.R₁.integers) = ⟨Jα, hJαint⟩ :=
      Subtype.ext (AlgEquiv.apply_symm_apply θ Jα)
    rw [e, hJαres]
  have hJθfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • Jθ = Jθ := by
    intro σ hσ
    apply θ.injective
    show θ (G σ • θ.symm Jα) = θ (θ.symm Jα)
    rw [hθgal, AlgEquiv.apply_symm_apply, hJαfix σ hσ]

  have one₁ : ∃ Bad : Finset (Place κ Fb), ∀ v : Place κ Fb, v ∉ Bad →
      ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Psp.IsStrictFst α β hα hβ δ W ∧ r₁ W = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W := by

    have hJint : Jα ∈ Rpd.R₁.integers := hJαint
    have hJres : (Rpd.R₁.residue ⟨Jα, hJint⟩ : Fb) = jb := hJαres
    have hJfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • Jα = Jα := hJαfix

    have hJ0 : (Jα : ↥(xHFunctionFieldBar M H)) ≠ 0 := by
      intro h0
      have : (Rpd.R₁.residue ⟨Jα, hJint⟩ : Fb) = 0 := by
        have e : (⟨Jα, hJint⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext h0
        rw [e, map_zero]
      exact hjb0 (hJres ▸ this)
    obtain ⟨DJ, hDJ, -⟩ := hPD.exists_divisor _ hJ0
    let BadPole : Finset (Place κ Fb) := (DJ.support.filter (fun W => DJ W < 0)).image r₁
    refine ⟨BadCrit ∪ hFixfin.toFinset ∪ BadPole ∪ Djb.support, fun v hv => ?_⟩
    have hvCrit : v ∉ BadCrit := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have hvfix : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v := fun h =>
      hv (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hFixfin.mem_toFinset.mpr h))))
    have hvPole : v ∉ BadPole := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvjb : v ∉ Djb.support := fun h => hv (Finset.mem_union_right _ h)

    have hjbv : v.ord (jb : Fb) = 0 := by
      have h0 : Djb v = 0 := Finsupp.notMem_support_iff.mp hvjb
      rw [hDjb] at h0; exact h0
    obtain ⟨hjbmem, hjbunit⟩ := Place.exists_isUnit_of_ord_eq_zero v hjb0 hjbv
    obtain ⟨c, hcval, -⟩ := Place.exists_hasValue_of_surjective v (hsurjb v) hjbmem
    have hvpos : 0 < v.ord (jb - algebraMap κ Fb c) := ord_sub_pos_of_hasValue' v hcval (hjbc c)
    have hcC : c ∉ C := by
      intro hc
      apply hvCrit
      refine Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_support_iff.mpr ?_⟩
      rw [hDc c v]; exact hvpos.ne'

    obtain ⟨y, hy⟩ := ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq A hA c
    let ct : ↥A := ⟨algebraMap _ (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩
    have hct : IsLocalRing.residue ↥A ct = c := hy
    have hctfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (ct : AlgebraicClosure ℚ) = ct := by
      intro σ hσ
      exact (IntermediateField.mem_fixedField_iff _ _).mp (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))).2 σ hσ

    let f : ↥(xHFunctionFieldBar M H) := Jα - algebraMap (AlgebraicClosure ℚ) _ (ct : AlgebraicClosure ℚ)
    have hctint : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ct : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers :=
      (Rpd.R₁.algebraMap_mem_iff _).mpr ct.2
    have hfint : f ∈ Rpd.R₁.integers := sub_mem hJint hctint
    have hfres : (Rpd.R₁.residue ⟨f, hfint⟩ : Fb) = jb - algebraMap κ Fb c := by
      have e : (⟨f, hfint⟩ : ↥Rpd.R₁.integers) = ⟨Jα, hJint⟩ - ⟨_, hctint⟩ := rfl
      rw [e, map_sub, hJres, Rpd.R₁.residue_algebraMap ct, hct]
    have hfres0 : Rpd.R₁.residue ⟨f, hfint⟩ ≠ 0 := by rw [hfres]; exact hjbc c
    have hffix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • f = f := by
      intro σ hσ
      show G σ • (Jα - _) = _
      rw [smul_sub, hJfix σ hσ, SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
      congr 2
      exact hctfix σ hσ
    have hf0 : f ≠ 0 := fun h => hfres0 (by
      have e : (⟨f, hfint⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext h
      rw [e, map_zero])
    obtain ⟨D, hD, -⟩ := hPD.exists_divisor f hf0

    have hv1 : v.ord (jb - algebraMap κ Fb c) = 1 := hC c hcC v hvpos

    have hnonneg : ∀ W, r₁ W = v → 0 ≤ D W := by
      intro W hW
      by_contra hneg
      push Not at hneg

      have hWJ : DJ W < 0 := by
        rw [hDJ]
        rw [hD] at hneg
        by_contra hge
        push Not at hge
        have hmemJ : (Jα : ↥(xHFunctionFieldBar M H)) ∈ W.toValuationSubring := Place.mem_of_ord_nonneg W hJ0 hge
        have hmemc : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ct : AlgebraicClosure ℚ) ∈ W.toValuationSubring := W.algebraMap_mem' _
        have hmemf : f ∈ W.toValuationSubring := sub_mem hmemJ hmemc
        exact (not_le.mpr hneg) (W.ord_nonneg_of_mem hmemf)
      exact hvPole (Finset.mem_image.mpr ⟨W, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hWJ.ne, hWJ⟩, hW⟩)

    have hlaw := hOS.1 f hfint hfres0 D hD v hvfix
    rw [hfres, hv1] at hlaw

    let E := Psp.fstDiv α β hα hβ δ D
    have hEdef : ∀ W, E W = if Psp.IsStrictFst α β hα hβ δ W then D W else 0 := fun W => by
      show (D.filter _) W = _; rw [Finsupp.filter_apply]
    have hEv : Finsupp.mapDomain (r₁) E v = ∑ W ∈ E.support.filter (fun W => r₁ W = v), E W := by
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [Finsupp.single_apply]
    have hsum : ∑ W ∈ E.support.filter (fun W => r₁ W = v), E W = 1 := by rw [← hEv]; exact hlaw
    have hEnn : ∀ W ∈ E.support.filter (fun W => r₁ W = v), 0 ≤ E W := by
      intro W hW
      obtain ⟨-, hWv⟩ := Finset.mem_filter.mp hW
      rw [hEdef]; split_ifs
      · exact hnonneg W hWv
      · exact le_rfl

    obtain ⟨W₀, hW₀mem, hW₀pos⟩ : ∃ W₀ ∈ E.support.filter (fun W => r₁ W = v), 0 < E W₀ := by
      by_contra hno
      push Not at hno
      have : ∑ W ∈ E.support.filter (fun W => r₁ W = v), E W ≤ 0 := Finset.sum_nonpos hno
      omega
    obtain ⟨hW₀supp, hW₀v⟩ := Finset.mem_filter.mp hW₀mem
    have hW₀strict : Psp.IsStrictFst α β hα hβ δ W₀ := by
      by_contra hns
      have : E W₀ = 0 := by rw [hEdef, if_neg hns]
      omega

    have huniq : ∀ W, Psp.IsStrictFst α β hα hβ δ W → r₁ W = v → 0 < D W → W = W₀ := by
      intro W hWs hWv hWpos
      by_contra hne
      have hEW : E W = D W := by rw [hEdef, if_pos hWs]
      have hEW₀ : 0 < E W₀ := hW₀pos
      have hWmem : W ∈ E.support.filter (fun W => r₁ W = v) :=
        Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hEW]; exact hWpos.ne'), hWv⟩
      have hpair : ({W, W₀} : Finset _) ⊆ E.support.filter (fun W => r₁ W = v) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hWmem
        · rw [Finset.mem_singleton.mp hx]; exact hW₀mem
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair (fun x hx _ => hEnn x hx)
      rw [Finset.sum_pair hne, hsum, hEW] at hle
      omega
    refine ⟨W₀, hW₀strict, hW₀v, fun σ hσ => ?_⟩

    have hread := hK2 σ hσ W₀
    have hSσ : Psp.IsStrictFst α β hα hβ δ (G σ • W₀) := by
      unfold JHPlaceSpecialization.IsStrictFst at hW₀strict ⊢
      rw [hread.1, hread.2]; exact hW₀strict
    have hDW₀ : 0 < D W₀ := by
      have : E W₀ = D W₀ := by rw [hEdef, if_pos hW₀strict]
      rw [← this]; exact hW₀pos
    have hordσ : (G σ • W₀).ord f = W₀.ord f := by
      have hσinv : σ⁻¹ ∈ A.inertiaSubgroupIn ℚ := inv_mem hσ
      conv_lhs => rw [← hffix σ hσ]
      exact SemilinearAut.ord_smul (G σ) W₀ f
    apply huniq _ hSσ (hread.1.trans hW₀v)
    rw [hD, hordσ, ← hD]; exact hDW₀

  have one₂ : ∃ Bad : Finset (Place κ Fb), ∀ v : Place κ Fb, v ∉ Bad →
      ∃ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        Psp.IsStrictSnd α β hα hβ δ W ∧ r₂ W = v ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • W = W := by

    have hJint : Jθ ∈ Rpd.R₂.integers := hJθint
    have hJres : (Rpd.R₂.residue ⟨Jθ, hJint⟩ : Fb) = jb := hJθres
    have hJfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • Jθ = Jθ := hJθfix

    have hJ0 : (Jθ : ↥(xHFunctionFieldBar M H)) ≠ 0 := by
      intro h0
      have : (Rpd.R₂.residue ⟨Jθ, hJint⟩ : Fb) = 0 := by
        have e : (⟨Jθ, hJint⟩ : ↥Rpd.R₂.integers) = 0 := Subtype.ext h0
        rw [e, map_zero]
      exact hjb0 (hJres ▸ this)
    obtain ⟨DJ, hDJ, -⟩ := hPD.exists_divisor _ hJ0
    let BadPole : Finset (Place κ Fb) := (DJ.support.filter (fun W => DJ W < 0)).image r₂
    refine ⟨BadCrit ∪ hFixfin.toFinset ∪ BadPole ∪ Djb.support, fun v hv => ?_⟩
    have hvCrit : v ∉ BadCrit := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have hvfix : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v := fun h =>
      hv (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hFixfin.mem_toFinset.mpr h))))
    have hvPole : v ∉ BadPole := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvjb : v ∉ Djb.support := fun h => hv (Finset.mem_union_right _ h)

    have hjbv : v.ord (jb : Fb) = 0 := by
      have h0 : Djb v = 0 := Finsupp.notMem_support_iff.mp hvjb
      rw [hDjb] at h0; exact h0
    obtain ⟨hjbmem, hjbunit⟩ := Place.exists_isUnit_of_ord_eq_zero v hjb0 hjbv
    obtain ⟨c, hcval, -⟩ := Place.exists_hasValue_of_surjective v (hsurjb v) hjbmem
    have hvpos : 0 < v.ord (jb - algebraMap κ Fb c) := ord_sub_pos_of_hasValue' v hcval (hjbc c)
    have hcC : c ∉ C := by
      intro hc
      apply hvCrit
      refine Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_support_iff.mpr ?_⟩
      rw [hDc c v]; exact hvpos.ne'

    obtain ⟨y, hy⟩ := ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq A hA c
    let ct : ↥A := ⟨algebraMap _ (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩
    have hct : IsLocalRing.residue ↥A ct = c := hy
    have hctfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (ct : AlgebraicClosure ℚ) = ct := by
      intro σ hσ
      exact (IntermediateField.mem_fixedField_iff _ _).mp (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))).2 σ hσ

    let f : ↥(xHFunctionFieldBar M H) := Jθ - algebraMap (AlgebraicClosure ℚ) _ (ct : AlgebraicClosure ℚ)
    have hctint : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ct : AlgebraicClosure ℚ) ∈ Rpd.R₂.integers :=
      (Rpd.R₂.algebraMap_mem_iff _).mpr ct.2
    have hfint : f ∈ Rpd.R₂.integers := sub_mem hJint hctint
    have hfres : (Rpd.R₂.residue ⟨f, hfint⟩ : Fb) = jb - algebraMap κ Fb c := by
      have e : (⟨f, hfint⟩ : ↥Rpd.R₂.integers) = ⟨Jθ, hJint⟩ - ⟨_, hctint⟩ := rfl
      rw [e, map_sub, hJres, Rpd.R₂.residue_algebraMap ct, hct]
    have hfres0 : Rpd.R₂.residue ⟨f, hfint⟩ ≠ 0 := by rw [hfres]; exact hjbc c
    have hffix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, G σ • f = f := by
      intro σ hσ
      show G σ • (Jθ - _) = _
      rw [smul_sub, hJfix σ hσ, SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
      congr 2
      exact hctfix σ hσ
    have hf0 : f ≠ 0 := fun h => hfres0 (by
      have e : (⟨f, hfint⟩ : ↥Rpd.R₂.integers) = 0 := Subtype.ext h
      rw [e, map_zero])
    obtain ⟨D, hD, -⟩ := hPD.exists_divisor f hf0

    have hv1 : v.ord (jb - algebraMap κ Fb c) = 1 := hC c hcC v hvpos

    have hnonneg : ∀ W, r₂ W = v → 0 ≤ D W := by
      intro W hW
      by_contra hneg
      push Not at hneg

      have hWJ : DJ W < 0 := by
        rw [hDJ]
        rw [hD] at hneg
        by_contra hge
        push Not at hge
        have hmemJ : (Jθ : ↥(xHFunctionFieldBar M H)) ∈ W.toValuationSubring := Place.mem_of_ord_nonneg W hJ0 hge
        have hmemc : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (ct : AlgebraicClosure ℚ) ∈ W.toValuationSubring := W.algebraMap_mem' _
        have hmemf : f ∈ W.toValuationSubring := sub_mem hmemJ hmemc
        exact (not_le.mpr hneg) (W.ord_nonneg_of_mem hmemf)
      exact hvPole (Finset.mem_image.mpr ⟨W, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hWJ.ne, hWJ⟩, hW⟩)

    have hlaw := hOS.2.1 f hfint hfres0 D hD v hvfix
    rw [hfres, hv1] at hlaw

    let E := Psp.sndDiv α β hα hβ δ D
    have hEdef : ∀ W, E W = if Psp.IsStrictSnd α β hα hβ δ W then D W else 0 := fun W => by
      show (D.filter _) W = _; rw [Finsupp.filter_apply]
    have hEv : Finsupp.mapDomain (r₂) E v = ∑ W ∈ E.support.filter (fun W => r₂ W = v), E W := by
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun W _ => ?_
      rw [Finsupp.single_apply]
    have hsum : ∑ W ∈ E.support.filter (fun W => r₂ W = v), E W = 1 := by rw [← hEv]; exact hlaw
    have hEnn : ∀ W ∈ E.support.filter (fun W => r₂ W = v), 0 ≤ E W := by
      intro W hW
      obtain ⟨-, hWv⟩ := Finset.mem_filter.mp hW
      rw [hEdef]; split_ifs
      · exact hnonneg W hWv
      · exact le_rfl

    obtain ⟨W₀, hW₀mem, hW₀pos⟩ : ∃ W₀ ∈ E.support.filter (fun W => r₂ W = v), 0 < E W₀ := by
      by_contra hno
      push Not at hno
      have : ∑ W ∈ E.support.filter (fun W => r₂ W = v), E W ≤ 0 := Finset.sum_nonpos hno
      omega
    obtain ⟨hW₀supp, hW₀v⟩ := Finset.mem_filter.mp hW₀mem
    have hW₀strict : Psp.IsStrictSnd α β hα hβ δ W₀ := by
      by_contra hns
      have : E W₀ = 0 := by rw [hEdef, if_neg hns]
      omega

    have huniq : ∀ W, Psp.IsStrictSnd α β hα hβ δ W → r₂ W = v → 0 < D W → W = W₀ := by
      intro W hWs hWv hWpos
      by_contra hne
      have hEW : E W = D W := by rw [hEdef, if_pos hWs]
      have hEW₀ : 0 < E W₀ := hW₀pos
      have hWmem : W ∈ E.support.filter (fun W => r₂ W = v) :=
        Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hEW]; exact hWpos.ne'), hWv⟩
      have hpair : ({W, W₀} : Finset _) ⊆ E.support.filter (fun W => r₂ W = v) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hWmem
        · rw [Finset.mem_singleton.mp hx]; exact hW₀mem
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hpair (fun x hx _ => hEnn x hx)
      rw [Finset.sum_pair hne, hsum, hEW] at hle
      omega
    refine ⟨W₀, hW₀strict, hW₀v, fun σ hσ => ?_⟩

    have hread := hK2 σ hσ W₀
    have hSσ : Psp.IsStrictSnd α β hα hβ δ (G σ • W₀) := by
      unfold JHPlaceSpecialization.IsStrictSnd at hW₀strict ⊢
      rw [hread.1, hread.2]; exact hW₀strict
    have hDW₀ : 0 < D W₀ := by
      have : E W₀ = D W₀ := by rw [hEdef, if_pos hW₀strict]
      rw [← this]; exact hW₀pos
    have hordσ : (G σ • W₀).ord f = W₀.ord f := by
      have hσinv : σ⁻¹ ∈ A.inertiaSubgroupIn ℚ := inv_mem hσ
      conv_lhs => rw [← hffix σ hσ]
      exact SemilinearAut.ord_smul (G σ) W₀ f
    apply huniq _ hSσ (hread.2.trans hW₀v)
    rw [hD, hordσ, ← hD]; exact hDW₀

  obtain ⟨Bad₁, hone₁⟩ := one₁
  obtain ⟨Bad₂, hone₂⟩ := one₂
  refine ⟨Bad₁ ∪ Bad₂, fun v hv => ⟨?_, ?_⟩⟩
  · obtain ⟨W, hWs, hWv, hWσ⟩ := hone₁ v (fun h => hv (Finset.mem_union_left _ h))
    exact ⟨W, hWs, hWv, hWσ⟩
  · obtain ⟨W, hWs, hWv, hWσ⟩ := hone₂ v (fun h => hv (Finset.mem_union_right _ h))
    exact ⟨W, hWs, hWv, hWσ⟩

end S_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_finset_forall_exists_isStrictFst_reduceFst_eq_and_isStrictSnd_reduceSnd_eq_forall_inertia_smul_eq_of_gammaLift (solution)
