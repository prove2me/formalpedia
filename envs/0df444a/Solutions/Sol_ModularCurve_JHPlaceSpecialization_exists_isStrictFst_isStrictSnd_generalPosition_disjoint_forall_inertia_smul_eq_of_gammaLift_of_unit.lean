-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ce322446-1488-5219-a63c-7a4de7d5ed23

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
import Theorems.Thm_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

section Generic

open AlgebraicCurve Module

namespace GenPosH

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_lSpace [IsAlgClosed K] [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by
      rw [IsCurveOver.deg_eq_one_of_isAlgClosed P]; norm_num
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := hRR D'
    have h0 : (0 : ℤ) ≤ (ell (Kc - D') : ℤ) := Int.natCast_nonneg _
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  haveI : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

theorem exists_generalPosition_of_infinite [IsAlgClosed K] [IsCurveOver K F]
    {Pl : Type*} (SF SSn : Pl → Prop) (rF rS : Pl → Place K F) (Inv : Pl → Prop) (Aff : Place K F → Prop)
    (W : Finset (Place K F)) (hWne : W.Nonempty) (B : Finset (Place K F))
    (Kc : Divisor K F) (g₀ : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀)
    (hS₁ : {t : Place K F | ∃ U : Pl, SF U ∧ rF U = t ∧ Inv U}.Infinite)
    (hS₂ : {t : Place K F | ∃ U : Pl, SSn U ∧ rS U = t ∧ Inv U}.Infinite)
    (hNA : {v : Place K F | ¬ Aff v}.Finite) :
    ∃ (d₁ d₂ : ℕ) (Q₁ : Fin d₁ → Pl) (Q₂ : Fin d₂ → Pl) (T₁ T₂ : Finset (Place K F)) (Qs : Pl),
      d₁ + 1 = g₀ + W.card ∧ d₂ = g₀ ∧
      (∀ i, SF (Q₁ i)) ∧ (∀ j, SSn (Q₂ j)) ∧
      (Function.Injective fun i => rF (Q₁ i)) ∧
      (Function.Injective fun j => rS (Q₂ j)) ∧
      (∀ v : Place K F, v ∈ T₁ ↔ ∃ i, rF (Q₁ i) = v) ∧
      (∀ v : Place K F, v ∈ T₂ ↔ ∃ j, rS (Q₂ j) = v) ∧
      Disjoint T₁ W ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, Aff v) ∧ (∀ v ∈ T₂, Aff v) ∧
      (∀ h : F, (∀ v : Place K F, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ W, w.HasValue h 0) → h = 0) ∧
      (∀ h : F, (∀ v : Place K F, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : K, h = algebraMap K F c) ∧
      SF Qs ∧ (∀ i, rF Qs ≠ rF (Q₁ i)) ∧
      (∀ i, Inv (Q₁ i)) ∧
      (∀ j, Inv (Q₂ j)) := by
  classical
  haveI hPD : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  set S₁ : Set (Place K F) := {t : Place K F | ∃ U : Pl, SF U ∧ rF U = t ∧ Inv U} with hS₁def
  set S₂ : Set (Place K F) := {t : Place K F | ∃ U : Pl, SSn U ∧ rS U = t ∧ Inv U} with hS₂def
  set NA : Set (Place K F) := {v : Place K F | ¬ Aff v} with hNAdef
  obtain ⟨t₀, U₀, -, -, -⟩ := hS₁.nonempty
  haveI : Nonempty Pl := ⟨U₀⟩
  classical
  obtain ⟨w₀, hw₀⟩ := hWne

  obtain ⟨T₂, hT₂S, hT₂card, hT₂ell⟩ :=
    AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Kc g₀ hRR Kc ((S₂ \ NA) \ ↑B)
      ((hS₂.diff hNA).diff B.finite_toSet)
  obtain ⟨T₁, hT₁S, hT₁card, hT₁ell⟩ :=
    AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Kc g₀ hRR
      (Kc + ∑ w ∈ W, Finsupp.single w 1) (((S₁ \ ↑W) \ NA) \ ↑B)
      (((hS₁.diff W.finite_toSet).diff hNA).diff B.finite_toSet)

  have hC : ConstantsAreBase K F :=
    constantsAreBase_of_deg_eq_one w₀ (IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
  have hell0 : ell (0 : Divisor K F) = 1 :=
    ell_zero_eq_one_of_constantsAreBase hC
  have hellK : ell Kc = g₀ := by
    have h := hRR 0
    rw [sub_zero, hell0, map_zero] at h
    push_cast at h
    omega
  have hdegK : Divisor.degree Kc = 2 * (g₀ : ℤ) - 2 := by
    have h := hRR Kc
    rw [sub_self, hell0, hellK] at h
    push_cast at h
    omega
  have hSW : ∀ u, (∑ w ∈ W, Finsupp.single w (1 : ℤ) : Divisor K F) u
      = if u ∈ W then 1 else 0 := by
    intro u
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hdegW : Divisor.degree (∑ w ∈ W, Finsupp.single w (1 : ℤ) : Divisor K F)
      = (W.card : ℤ) := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hellKW : ell (Kc + ∑ w ∈ W, Finsupp.single w 1) + 1 = g₀ + W.card := by
    have h := hRR (Kc + ∑ w ∈ W, Finsupp.single w 1)
    have hneg : ell (Kc - (Kc + ∑ w ∈ W, Finsupp.single w 1)) = 0 := by
      rw [sub_add_cancel_left, ell, lSpace_eq_bot_of_degree_neg, finrank_bot]
      rw [map_neg, hdegW, neg_lt_zero]
      exact_mod_cast Finset.card_pos.mpr ⟨w₀, hw₀⟩
    rw [hneg, map_add, hdegK, hdegW] at h
    push_cast at h
    have hWpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨w₀, hw₀⟩
    omega

  have hl₁ : ∀ t ∈ T₁, ∃ Q : Pl,
      SF Q ∧ rF Q = t ∧
        Inv Q :=
    fun t ht => (hT₁S ht).1.1.1
  have hl₂ : ∀ t ∈ T₂, ∃ Q : Pl,
      SSn Q ∧ rS Q = t ∧
        Inv Q :=
    fun t ht => (hT₂S ht).1.1
  choose! L₁ hL₁ using hl₁
  choose! L₂ hL₂ using hl₂
  have hT₁NA : ∀ v ∈ T₁, Aff v := fun v hv => by
    by_contra h; exact (hT₁S hv).1.2 h
  have hT₂NA : ∀ v ∈ T₂, Aff v := fun v hv => by
    by_contra h; exact (hT₂S hv).1.2 h

  obtain ⟨ts, hts⟩ := (hS₁.diff T₁.finite_toSet).nonempty
  obtain ⟨⟨Qs, hQs, hQsred, -⟩, htsT⟩ := hts
  refine ⟨T₁.card, T₂.card, fun i => L₁ (T₁.equivFin.symm i), fun j => L₂ (T₂.equivFin.symm j),
    T₁, T₂, Qs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hQs, ?_, ?_, ?_⟩
  · rw [hT₁card]; exact hellKW
  · rw [hT₂card, hellK]
  · intro i; exact (hL₁ _ (T₁.equivFin.symm i).2).1
  · intro j; exact (hL₂ _ (T₂.equivFin.symm j).2).1
  · intro i j hij
    have h : rF (L₁ (T₁.equivFin.symm i)) = rF (L₁ (T₁.equivFin.symm j)) := hij
    rw [(hL₁ _ (T₁.equivFin.symm i).2).2.1, (hL₁ _ (T₁.equivFin.symm j).2).2.1] at h
    exact T₁.equivFin.symm.injective (Subtype.ext h)
  · intro i j hij
    have h : rS (L₂ (T₂.equivFin.symm i)) = rS (L₂ (T₂.equivFin.symm j)) := hij
    rw [(hL₂ _ (T₂.equivFin.symm i).2).2.1, (hL₂ _ (T₂.equivFin.symm j).2).2.1] at h
    exact T₂.equivFin.symm.injective (Subtype.ext h)
  · intro v
    constructor
    · intro hv
      refine ⟨T₁.equivFin ⟨v, hv⟩, ?_⟩
      rw [(hL₁ _ (T₁.equivFin.symm _).2).2.1, Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      rw [(hL₁ _ (T₁.equivFin.symm i).2).2.1]
      exact (T₁.equivFin.symm i).2
  · intro v
    constructor
    · intro hv
      refine ⟨T₂.equivFin ⟨v, hv⟩, ?_⟩
      rw [(hL₂ _ (T₂.equivFin.symm _).2).2.1, Equiv.symm_apply_apply]
    · rintro ⟨j, rfl⟩
      rw [(hL₂ _ (T₂.equivFin.symm j).2).2.1]
      exact (T₂.equivFin.symm j).2
  · exact Finset.disjoint_left.mpr fun v hv hvW => (hT₁S hv).1.1.2 hvW
  · exact Finset.disjoint_left.mpr fun v hv hvB => (hT₁S hv).2 hvB
  · exact Finset.disjoint_left.mpr fun v hv hvB => (hT₂S hv).2 hvB
  · exact hT₁NA
  · exact hT₂NA
  ·
    intro h hreg hsimple hval
    by_contra h0
    set D : Divisor K F :=
      ∑ v ∈ T₁, Finsupp.single v 1 - ∑ w ∈ W, Finsupp.single w 1 with hDdef
    have hST : ∀ u, (∑ v ∈ T₁, Finsupp.single v (1 : ℤ) : Divisor K F) u
        = if u ∈ T₁ then 1 else 0 := by
      intro u
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hDapp : ∀ u, D u = (if u ∈ T₁ then 1 else 0) - (if u ∈ W then 1 else 0) := by
      intro u; rw [hDdef, Finsupp.sub_apply, hST, hSW]
    have hdisj : ∀ u, u ∈ W → u ∉ T₁ := fun u huW huT =>
      (hT₁S huT).1.1.2 huW
    have hordW : ∀ w ∈ W, 1 ≤ w.ord h := by
      intro w hw
      obtain ⟨hm, hres⟩ := hval w hw
      rw [map_zero, IsLocalRing.residue_eq_zero_iff] at hres
      have hnu : ¬ IsUnit (⟨h, hm⟩ : w.toValuationSubring) :=
        (IsLocalRing.mem_maximalIdeal _).mp hres
      have hnn := w.ord_nonneg_of_mem hm
      by_contra hlt
      have h00 : w.ord h = 0 := by omega
      obtain ⟨hm', hu⟩ := w.exists_isUnit_of_ord_eq_zero h0 h00
      exact hnu hu
    have hmem : h ∈ LSpace D := by
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun u => ?_
      rw [hDapp]
      by_cases huW : u ∈ W
      · rw [if_neg (hdisj u huW), if_pos huW]; have := hordW u huW; omega
      · by_cases huT : u ∈ T₁
        · rw [if_pos huT, if_neg huW]; have := hsimple u huT; omega
        · rw [if_neg huT, if_neg huW]; have := hreg u huT; omega
    have hdegT : Divisor.degree (∑ v ∈ T₁, Finsupp.single v (1 : ℤ) : Divisor K F)
        = (T₁.card : ℤ) := by
      rw [map_sum]
      simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hdegD : Divisor.degree D = (T₁.card : ℤ) - W.card := by
      rw [hDdef, map_sub, hdegT, hdegW]
    have hKD : Kc - D = Kc + ∑ w ∈ W, Finsupp.single w 1 - ∑ v ∈ T₁, Finsupp.single v 1 := by
      rw [hDdef, sub_sub_eq_add_sub]
    have hellD : ell D = 0 := by
      have h1 := hRR D
      rw [hKD, hT₁ell, hdegD, hT₁card] at h1
      push_cast at h1
      have h3 : ((ell (Kc + ∑ w ∈ W, Finsupp.single w 1) : ℕ) : ℤ) + 1 = g₀ + W.card := by
        exact_mod_cast hellKW
      omega
    have hfin : Module.Finite K (LSpace D) := by
      exact finite_lSpace hRR w₀ D
    have hbot : (⊥ : Submodule K F) = LSpace D :=
      Submodule.eq_of_le_of_finrank_eq bot_le (by rw [finrank_bot]; exact hellD.symm)
    rw [← hbot, Submodule.mem_bot] at hmem
    exact h0 hmem
  ·
    intro h hreg hsimple
    set D : Divisor K F := ∑ v ∈ T₂, Finsupp.single v 1 with hDdef
    have hDapp : ∀ u, D u = if u ∈ T₂ then 1 else 0 := by
      intro u
      rw [hDdef, Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hmem : h ∈ LSpace D := by
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne h 0 with rfl | h0
      · exact Or.inl rfl
      · refine Or.inr fun u => ?_
        rw [hDapp]
        split_ifs with hu
        · have := hsimple u hu; omega
        · have := hreg u hu; omega
    have hdeg : Divisor.degree D = (T₂.card : ℤ) := by
      rw [hDdef, map_sum]
      simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hellD : ell D = 1 := by
      have h1 := hRR D
      have h2 : Kc - D = Kc - ∑ v ∈ T₂, Finsupp.single v 1 := rfl
      rw [hdeg, hT₂card, hellK, h2, hT₂ell] at h1
      push_cast at h1
      omega
    have hle : LinearMap.range (Algebra.linearMap K F) ≤ LSpace D := by
      rintro _ ⟨c, rfl⟩
      refine lSpace_mono (D := 0) ?_ (algebraMap_mem_lSpace_zero c)
      intro u
      rw [hDapp]
      split_ifs <;> simp
    have hfin : Module.Finite K (LSpace D) := by
      exact finite_lSpace hRR w₀ D
    have heq : LinearMap.range (Algebra.linearMap K F) = LSpace D := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [LinearMap.finrank_range_of_inj (algebraMap K F).injective,
        Module.finrank_self]
      exact hellD.symm
    rw [← heq] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  · intro i h
    rw [hQsred, (hL₁ _ (T₁.equivFin.symm i).2).2.1] at h
    exact htsT (by rw [Finset.mem_coe, h]; exact (T₁.equivFin.symm i).2)
  · intro i
    exact (hL₁ _ (T₁.equivFin.symm i).2).2.2
  · intro j
    exact (hL₂ _ (T₂.equivFin.symm j).2).2.2

end GenPosH

end Generic

open AlgebraicCurve IsLocalRing ModularCurve in

private theorem GenPosH.surjective_algebraMap_residueField_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (v : Place K F) (h : v.deg = 1) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  have h' : Module.finrank K v.ResidueField = Nat.succ 0 := h
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_eq_succ h'
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

set_option maxHeartbeats 3200000 in
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

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (Kc : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (g₀ : ℕ)
    (hRR : ∀ D : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀) :
    ∃ (d₁ d₂ : ℕ) (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      d₁ + 1 = g₀ + (SS.image Prod.fst).card ∧ d₂ = g₀ ∧
      (∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) ∧ (∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j)) ∧
      (Function.Injective fun i => Psp.reduceFst α hα (Q₁ i)) ∧
      (Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j)) ∧
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) ∧
      (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v) ∧
      Disjoint T₁ (SS.image Prod.fst) ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) ∧ (∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) ∧
      (∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0) ∧
      (∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c) ∧
      Psp.IsStrictFst α β hα hβ δ Qs ∧ (∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁ i)) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Q₂ j = Q₂ j) := by
  classical

  haveI hIC : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    (ModularCurve.isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A
      (JHNeronObjectAtP.ΓN p M H hpM) (translation_mem_GammaH _ _)).1
  haveI hPD : HasPrincipalDivisors (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := IsCurveOver.hasPrincipalDivisors

  have hp : p.Prime := Fact.out
  have hpMp : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    have h1 : p * p ∣ M / p * p := Nat.mul_dvd_mul_right h p
    rw [Nat.div_mul_cancel hpM] at h1
    simpa [pow_two] using h1
  have hWne : (SS.image Prod.fst).Nonempty := by
    obtain ⟨y, hy⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (JHNeronObjectAtP.ΓN p M H hpM)
      (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM)) (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM))
      p hpMp (ResidueField ↥A)
    refine ⟨qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y, Finset.mem_image.mpr ?_⟩
    exact ⟨(qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y, y),
      (hSS _).mpr (frob_mk_mem_ssNodePairsQExp hy), rfl⟩

  have hS₁ : {t : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | ∃ U : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.IsStrictFst α β hα hβ δ U ∧ Psp.reduceFst α hα U = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • U = U}.Infinite := by
    intro hfin
    obtain ⟨Q₁, Q₂, h1, -, -, -, hB, -, hfix, -⟩ :=
      ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
        p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit
        hfin.toFinset 1 0
    exact hB 0 (hfin.mem_toFinset.mpr ⟨Q₁ 0, h1 0, rfl, hfix 0⟩)
  have hS₂ : {t : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | ∃ U : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.IsStrictSnd α β hα hβ δ U ∧ Psp.reduceSnd β hβ δ U = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • U = U}.Infinite := by
    intro hfin
    obtain ⟨Q₁, Q₂, -, h2, -, -, -, hB, -, hfix⟩ :=
      ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
        p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit
        hfin.toFinset 0 1
    exact hB 0 (hfin.mem_toFinset.mpr ⟨Q₂ 0, h2 0, rfl, hfix 0⟩)

  have hNA : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A v}.Finite := by
    obtain ⟨x, hx⟩ : ∃ x : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) :=
      ⟨⟨jqModC (ResidueField ↥A), intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC (ResidueField ↥A) _)⟩, rfl⟩
    have hx0 : x ≠ 0 := by
      intro h
      have hc : ((x : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)).coeff (-1) = 0 := by rw [h]; simp
      rw [hx, coeff_jqModC_neg_one] at hc
      exact one_ne_zero hc
    obtain ⟨Dx, hDx, -⟩ := hPD.exists_divisor x hx0
    refine Dx.support.finite_toSet.subset ?_
    intro v hv
    rw [Set.mem_setOf_eq] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDx]
    intro h0
    have hmem : x ∈ v.toValuationSubring := v.mem_of_ord_nonneg hx0 (le_of_eq h0.symm)
    obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective
      (GenPosH.surjective_algebraMap_residueField_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)) hmem
    exact hv ⟨x, a, hx, ha⟩
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, h⟩ :=
    GenPosH.exists_generalPosition_of_infinite
      (Psp.IsStrictFst α β hα hβ δ) (Psp.IsStrictSnd α β hα hβ δ) (Psp.reduceFst α hα) (Psp.reduceSnd β hβ δ)
      (fun U => ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • U = U)
      (JHPlaceSpecialization.IsAffinePlace p M H hpM A)
      (SS.image Prod.fst) hWne B Kc g₀ hRR hS₁ hS₂ hNA
  exact ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, h⟩

end S_ModularCurve_JHPlaceSpecialization_exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit (solution)
