-- Prove2me | solution 1 for ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8bc5bea1-1ad4-50da-b5f9-b24fefd15db8

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace P2MK1

theorem comb (g d : ℕ) (hd : d = 2 * g + 1) (S : Finset ℕ) (hS : ∀ s ∈ S, s ≤ d) (h0 : 0 ∈ S) (hdS : d ∈ S)
    (hcard : S.card = g + 2) (hclosed : ∀ a ∈ S, ∀ b ∈ S, a + b ≤ d → a + b ∈ S) :
    ∀ m, d < m → m ≤ 2 * d → ∃ a ∈ S, ∃ b ∈ S, a + b = m := by
  classical
  intro m hm1 hm2
  set x : ℕ := m - d with hx
  have hx1 : 1 ≤ x := by omega
  have hxd : x ≤ d := by omega
  have hxm : x + d = m := by omega
  by_cases hxS : x ∈ S
  · exact ⟨x, hxS, d, hdS, hxm⟩
  by_contra hno
  push Not at hno

  set A := S.filter (fun s => x ≤ s) with hA
  set Hlo := S.filter (fun s => s < x) with hHlo
  have hsplit : A.card + Hlo.card = S.card := by
    rw [hA, hHlo]
    have := Finset.card_filter_add_card_filter_not (s := S) (fun s => x ≤ s)
    convert this using 3
    ext s; simp [not_le]

  set U := A.image (fun s => s - x) with hU
  set V := A.image (fun s => d - s) with hV
  have hUsub : U ⊆ Finset.range (d - x + 1) := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    have := hS s (Finset.mem_filter.mp hs).1
    exact Finset.mem_range.mpr (by omega)
  have hVsub : V ⊆ Finset.range (d - x + 1) := by
    intro j hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
    have := (Finset.mem_filter.mp hs).2
    exact Finset.mem_range.mpr (by omega)
  have hUcard : U.card = A.card := by
    apply Finset.card_image_of_injOn
    intro s₁ hs₁ s₂ hs₂ h
    have h1 := (Finset.mem_filter.mp hs₁).2; have h2 := (Finset.mem_filter.mp hs₂).2
    simp only at h
    omega
  have hVcard : V.card = A.card := by
    apply Finset.card_image_of_injOn
    intro s₁ hs₁ s₂ hs₂ h
    have h1 := hS s₁ (Finset.mem_filter.mp hs₁).1; have h2 := hS s₂ (Finset.mem_filter.mp hs₂).1
    simp only at h
    omega
  have hdisj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro j hjU hjV
    obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp hjU
    obtain ⟨s₂, hs₂, hj⟩ := Finset.mem_image.mp hjV
    have h1 := Finset.mem_filter.mp hs₁; have h2 := Finset.mem_filter.mp hs₂
    have := hS s₂ h2.1
    apply hno s₁ h1.1 s₂ h2.1
    omega
  have hA2 : 2 * A.card ≤ d - x + 1 := by
    have := Finset.card_le_card (Finset.union_subset hUsub hVsub)
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hVcard, Finset.card_range] at this
    omega

  have hlo2 : 2 * Hlo.card ≤ x + 1 := by
    set W := Hlo.image (fun s => x - s) with hW
    have hWcard : W.card = Hlo.card := by
      apply Finset.card_image_of_injOn
      intro s₁ hs₁ s₂ hs₂ h
      have h1 := (Finset.mem_filter.mp hs₁).2; have h2 := (Finset.mem_filter.mp hs₂).2
      simp only at h
      omega
    have hWsub : W ⊆ Finset.Icc 1 x \ S := by
      intro j hj
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
      have h1 := Finset.mem_filter.mp hs
      rw [Finset.mem_sdiff, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, fun hmem => hxS ?_⟩
      have := hclosed s h1.1 (x - s) hmem (by omega)
      rwa [show s + (x - s) = x by omega] at this
    have hsub2 : Hlo.erase 0 ⊆ Finset.Icc 1 x ∩ S := by
      intro s hs
      rw [Finset.mem_erase] at hs
      have h1 := Finset.mem_filter.mp hs.2
      rw [Finset.mem_inter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, h1.1⟩
    have h0lo : 0 ∈ Hlo := Finset.mem_filter.mpr ⟨h0, by omega⟩
    have hc1 := Finset.card_le_card hWsub
    have hc2 := Finset.card_le_card hsub2
    rw [Finset.card_erase_of_mem h0lo] at hc2
    have hc3 : (Finset.Icc 1 x \ S).card + (Finset.Icc 1 x ∩ S).card = x := by
      rw [Finset.card_sdiff_add_card_inter, Nat.card_Icc]; omega
    omega
  omega

end P2MK1

namespace P2MK1

open AlgebraicCurve ModularCurve Submodule

section OnePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem rr_mono {D D' : Divisor K F} (h : D ≤ D') : riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (h v)).trans h1)

theorem mul_mem_rr {A B : Divisor K F} {f g : F} (hf : f ∈ riemannRochSpace A) (hg : g ∈ riemannRochSpace B) :
    f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem rr_mul_le (A B : Divisor K F) : riemannRochSpace A * riemannRochSpace B ≤ riemannRochSpace (A + B) := by
  rw [mul_le]; intro f hf g hg; exact mul_mem_rr hf hg

theorem mem_rr_single_of_ord (o : Place K F) {m k : ℤ} {f : F}
    (hf : f ∈ riemannRochSpace (m • Finsupp.single o 1)) (hk : f = 0 ∨ -k ≤ o.ord f) :
    f ∈ riemannRochSpace (k • Finsupp.single o 1) := by
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro w
  by_cases hw : w = o
  · subst hw; simpa using hk
  · have := hf w
    simpa [Finsupp.single_apply, Ne.symm hw, hw] using this

def Realised (V : Submodule K F) (o : Place K F) (j : ℤ) : Prop := ∃ f ∈ V, f ≠ 0 ∧ o.ord f = -j

theorem evalAt_add_of_mem (o : Place K F) (ho : o.IsRational) {f g : F}
    (hf : f ∈ o.toValuationSubring) (hg : g ∈ o.toValuationSubring) :
    o.evalAt (f + g) = o.evalAt f + o.evalAt g := by
  apply o.algebraMap_residueField_injective
  rw [map_add, o.algebraMap_evalAt ho (add_mem hf hg), o.algebraMap_evalAt ho hf, o.algebraMap_evalAt ho hg, ← map_add]
  rfl

theorem evalAt_smul_of_mem (o : Place K F) (ho : o.IsRational) (a : K) {f : F} (hf : f ∈ o.toValuationSubring) :
    o.evalAt (a • f) = a * o.evalAt f := by
  rw [Algebra.smul_def, o.evalAt_mul_of_mem ho (o.algebraMap_mem' a) hf, o.evalAt_algebraMap_eq]

theorem ord_eq_zero_of_evalAt_ne_zero (o : Place K F) (ho : o.IsRational) {f : F}
    (hf : f ∈ o.toValuationSubring) (h : o.evalAt f ≠ 0) : o.ord f = 0 := by
  have hres : IsLocalRing.residue o.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply o.algebraMap_residueField_injective
    rw [o.algebraMap_evalAt ho hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := o.ord_coe_unit u
  rwa [hu] at this

theorem finrank_inf_succ (o : Place K F) (ho : o.IsRational) {π : F} (hπ : o.ord π = 1)
    (V : Submodule K F) {m : ℤ} (hV : V ≤ riemannRochSpace (m • Finsupp.single o 1))
    [FiniteDimensional K ↥V] (k : ℤ) [Decidable (Realised V o (k + 1))] :
    Module.finrank K ↥(V ⊓ riemannRochSpace ((k + 1) • Finsupp.single o 1))
      = Module.finrank K ↥(V ⊓ riemannRochSpace (k • Finsupp.single o 1))
        + (if Realised V o (k + 1) then 1 else 0) := by
  classical
  have hπ0 : π ≠ 0 := fun h => by rw [h, o.ord_zero] at hπ; exact zero_ne_one hπ
  set W : Submodule K F := V ⊓ riemannRochSpace ((k + 1) • Finsupp.single o 1) with hW
  set W' : Submodule K F := V ⊓ riemannRochSpace (k • Finsupp.single o 1) with hW'
  haveI : FiniteDimensional K ↥W := Submodule.finiteDimensional_of_le inf_le_left
  have hle : W' ≤ W := inf_le_inf_left V (rr_mono (by
    intro w; simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]; split_ifs <;> omega))

  have hint : ∀ f ∈ W, f * π ^ (k + 1) ∈ o.toValuationSubring := by
    intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [zero_mul]; exact zero_mem _
    apply o.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hf0 (zpow_ne_zero _ hπ0))
    have := (mem_riemannRochSpace_iff.mp hf.2 o).resolve_left hf0
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
    rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one]
    omega

  let lc : ↥W →ₗ[K] K :=
    { toFun := fun f => o.evalAt ((f : F) * π ^ (k + 1))
      map_add' := fun f g => by
        simp only [Submodule.coe_add, add_mul]
        exact evalAt_add_of_mem o ho (hint _ f.2) (hint _ g.2)
      map_smul' := fun c f => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc]
        exact evalAt_smul_of_mem o ho c (hint _ f.2) }

  have hker : ∀ f : ↥W, lc f = 0 ↔ (f : F) ∈ W' := by
    intro f
    constructor
    · intro h0
      refine ⟨f.2.1, mem_rr_single_of_ord o (hV f.2.1) ?_⟩
      rcases eq_or_ne (f : F) 0 with hf0 | hf0
      · exact Or.inl hf0
      right

      have hmem := hint _ f.2
      have hne0 : (f : F) * π ^ (k + 1) ≠ 0 := mul_ne_zero hf0 (zpow_ne_zero _ hπ0)
      have hnn : 0 ≤ o.ord ((f : F) * π ^ (k + 1)) := by
        have := (mem_riemannRochSpace_iff.mp f.2.2 o).resolve_left hf0
        simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
        rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one]; omega
      have hne : o.ord ((f : F) * π ^ (k + 1)) ≠ 0 := by
        intro h00
        exact (o.evalAt_ne_zero_of_ord_eq_zero ho hne0 h00) h0
      have : 1 ≤ o.ord ((f : F) * π ^ (k + 1)) := by omega
      rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one] at this
      omega
    · intro hf'
      rcases eq_or_ne (f : F) 0 with hf0 | hf0
      · show o.evalAt ((f : F) * π ^ (k + 1)) = 0
        rw [hf0, zero_mul]; exact (o.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
      have := (mem_riemannRochSpace_iff.mp hf'.2 o).resolve_left hf0
      simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
      by_contra hne
      have h00 := ord_eq_zero_of_evalAt_ne_zero o ho (hint _ f.2) hne
      rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one] at h00
      omega

  let e : ↥W' →ₗ[K] ↥(LinearMap.ker lc) :=
    { toFun := fun f => ⟨⟨(f : F), hle f.2⟩, (LinearMap.mem_ker).mpr ((hker ⟨f, hle f.2⟩).mpr f.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hebij : Function.Bijective e := by
    constructor
    · intro a b h; exact Subtype.ext (congrArg (fun z : ↥(LinearMap.ker lc) => ((z : ↥W) : F)) h)
    · rintro ⟨f, hf⟩
      exact ⟨⟨(f : F), (hker f).mp (LinearMap.mem_ker.mp hf)⟩, rfl⟩
  have hkerdim : Module.finrank K ↥(LinearMap.ker lc) = Module.finrank K ↥W' :=
    (LinearEquiv.ofBijective e hebij).finrank_eq.symm

  have hrn := LinearMap.finrank_range_add_finrank_ker lc
  rw [hkerdim] at hrn
  have hrange_le : Module.finrank K ↥(LinearMap.range lc) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range lc)
    rwa [Module.finrank_self] at this
  split_ifs with hreal
  ·
    obtain ⟨f, hfV, hf0, hordf⟩ := hreal
    have hfW : f ∈ W := ⟨hfV, mem_rr_single_of_ord o (hV hfV) (Or.inr (by rw [hordf]))⟩
    have hlcf : lc ⟨f, hfW⟩ ≠ 0 := by
      show o.evalAt (f * π ^ (k + 1)) ≠ 0
      apply o.evalAt_ne_zero_of_ord_eq_zero ho (mul_ne_zero hf0 (zpow_ne_zero _ hπ0))
      rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one, hordf]; ring
    have hpos : 0 < Module.finrank K ↥(LinearMap.range lc) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨lc ⟨f, hfW⟩, LinearMap.mem_range_self _ _⟩, fun h => hlcf (congrArg Subtype.val h)⟩
    omega
  ·
    have hzero : Module.finrank K ↥(LinearMap.range lc) = 0 := by
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      ext f
      by_contra hne
      apply hreal
      rcases eq_or_ne (f : F) 0 with hf0 | hf0
      · apply absurd _ hne
        show o.evalAt ((f : F) * π ^ (k + 1)) = 0
        rw [hf0, zero_mul]; exact (o.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
      refine ⟨f, f.2.1, hf0, ?_⟩
      have h00 := ord_eq_zero_of_evalAt_ne_zero o ho (hint _ f.2) hne
      rw [o.ord_mul hf0 (zpow_ne_zero _ hπ0), o.ord_zpow, hπ, mul_one] at h00
      omega
    omega

theorem finrank_eq_card_realised (o : Place K F) (ho : o.IsRational) {π : F} (hπ : o.ord π = 1)
    (hbot : riemannRochSpace ((-1 : ℤ) • Finsupp.single o 1) = ⊥)
    (V : Submodule K F) (m : ℕ) (hV : V ≤ riemannRochSpace ((m : ℤ) • Finsupp.single o 1))
    [FiniteDimensional K ↥V] [DecidablePred (fun j : ℕ => Realised V o j)] :
    Module.finrank K ↥V = ((Finset.range (m + 1)).filter (fun j : ℕ => Realised V o j)).card := by
  classical

  have P : ∀ n : ℕ, Module.finrank K ↥(V ⊓ riemannRochSpace (((n : ℤ) - 1) • Finsupp.single o 1))
      = ((Finset.range n).filter (fun j : ℕ => Realised V o j)).card := by
    intro n
    induction n with
    | zero =>
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, hbot, inf_bot_eq, finrank_bot]
      simp
    | succ n ih =>
      have step := finrank_inf_succ o ho hπ V hV ((n : ℤ) - 1)
      have hc1 : (n : ℤ) - 1 + 1 = (n : ℤ) := by ring
      rw [hc1] at step
      have hc2 : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
      have hnot : n ∉ (Finset.range n).filter (fun j : ℕ => Realised V o j) := by simp
      rw [hc2, step, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : Realised V o (n : ℤ)
      · simp [h, Finset.card_insert_of_notMem hnot]
      · simp [h]
  have := P (m + 1)
  rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) by push_cast; ring, inf_eq_left.mpr hV] at this
  exact this

end OnePlace

end P2MK1

namespace P2MK1

open AlgebraicCurve ModularCurve Submodule KaehlerDifferential

section Bar

variable (N : ℕ) [NeZero N]

theorem ell_eq_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hCD : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
    hasCanonicalDivisor_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

set_option maxHeartbeats 6400000 in
theorem main :
    riemannRochSpace (embDivisor N) * riemannRochSpace (embDivisor N)
      = riemannRochSpace ((2 : ℤ) • embDivisor N) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  set o := cuspInftyBar N with ho_def
  set g : ℕ := genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) with hg
  set d : ℕ := embDegree N with hd_def
  have hd : d = 2 * g + 1 := rfl
  have hE : embDivisor N = (d : ℤ) • Finsupp.single o 1 := rfl
  have h2E : (2 : ℤ) • embDivisor N = ((2 * d : ℕ) : ℤ) • Finsupp.single o 1 := by
    rw [hE, smul_smul]; push_cast; ring_nf

  have hdego : ∀ n : ℤ, Divisor.degree (n • Finsupp.single o 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) = n := by
    intro n; rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
  have hfinrank : ∀ n : ℕ, 2 * g ≤ n + 1 →
      (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace ((n : ℤ) • Finsupp.single o 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))) : ℤ) = n + 1 - g := by
    intro n hn
    have := ell_eq_bar N ((n : ℤ) • Finsupp.single o 1) (by rw [hdego]; omega)
    rw [hdego] at this; exact this

  have hrat : o.IsRational := (Place.isRational_iff_deg_eq_one o).mpr (deg_eq_one_modularFunctionFieldBar N o)
  obtain ⟨π, hπ⟩ := Place.exists_ord_eq_one o
  have hbot : riemannRochSpace ((-1 : ℤ) • Finsupp.single o 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) = ⊥ := by
    have := AlgebraicCurve.lSpace_eq_bot_of_degree_neg (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
      (D := (-1 : ℤ) • Finsupp.single o 1) (by rw [hdego]; norm_num)
    exact this

  set LE : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := riemannRochSpace (embDivisor N) with hLE
  set L2 : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := riemannRochSpace ((2 : ℤ) • embDivisor N) with hL2
  set V : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := LE * LE with hVdef
  have hVle : V ≤ L2 := by
    rw [hVdef, hL2, two_smul]; exact rr_mul_le _ _
  have hL2fin : FiniteDimensional (AlgebraicClosure ℚ) ↥L2 := by
    apply Module.finite_of_finrank_pos
    have := hfinrank (2 * d) (by omega)
    rw [← h2E] at this
    have : (0 : ℤ) < Module.finrank (AlgebraicClosure ℚ) ↥L2 := by rw [hL2, this]; push_cast; omega
    exact_mod_cast this
  haveI := hL2fin
  haveI hVfin : FiniteDimensional (AlgebraicClosure ℚ) ↥V := Submodule.finiteDimensional_of_le hVle
  have hLEle : LE ≤ L2 := by
    rw [hLE, hL2, hE, smul_smul]; exact rr_mono (by intro w; simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]; split_ifs <;> omega)
  haveI hLEfin : FiniteDimensional (AlgebraicClosure ℚ) ↥LE := Submodule.finiteDimensional_of_le hLEle

  set S : Finset ℕ := (Finset.range (d + 1)).filter (fun j : ℕ => Realised LE o j) with hSdef
  have hS_le : ∀ s ∈ S, s ≤ d := fun s hs => by have := Finset.mem_range.mp (Finset.mem_filter.mp hs).1; omega
  have hS_mem : ∀ j : ℕ, j ∈ S ↔ j ≤ d ∧ Realised LE o j := fun j => by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
  have hScard : S.card = g + 2 := by
    have h1 := finrank_eq_card_realised o hrat hπ hbot LE d (by rw [hLE, hE])
    have h2 := hfinrank d (by omega)
    rw [← hE, ← hLE, h1] at h2
    have : (S.card : ℤ) = d + 1 - g := h2
    omega
  have h0S : 0 ∈ S := by
    rw [hS_mem]; refine ⟨by omega, 1, ?_, one_ne_zero, by simp⟩
    rw [hLE, mem_riemannRochSpace_iff]; intro w; right
    rw [Place.ord_one]; simp only [hE, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]; split_ifs <;> simp
  have hdS : d ∈ S := by

    rw [hS_mem]; refine ⟨le_rfl, ?_⟩
    have hsub : riemannRochSpace (((d : ℤ) - 1) • Finsupp.single o 1) ≤ LE := by
      rw [hLE, hE]; exact rr_mono (by intro w; simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]; split_ifs <;> omega)
    have hlt : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (((d : ℤ) - 1) • Finsupp.single o 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))) < Module.finrank (AlgebraicClosure ℚ) ↥LE := by
      have h1 := hfinrank (d - 1) (by omega)
      have h2 := hfinrank d (by omega)
      rw [← hE, ← hLE] at h2
      have hc : (((d - 1 : ℕ) : ℤ)) = (d : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
      rw [hc] at h1
      have : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (((d : ℤ) - 1) • Finsupp.single o 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))) : ℤ) < Module.finrank (AlgebraicClosure ℚ) ↥LE := by
        rw [h1, h2]; push_cast; omega
      exact_mod_cast this
    obtain ⟨f, hfE, hfnot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hsub fun heq => by rw [heq] at hlt; exact lt_irrefl _ hlt)
    have hf0 : f ≠ 0 := fun h0 => hfnot (h0 ▸ Submodule.zero_mem _)
    refine ⟨f, hfE, hf0, ?_⟩
    have hge := (mem_riemannRochSpace_iff.mp (show f ∈ riemannRochSpace ((d : ℤ) • Finsupp.single o 1) by rw [← hE, ← hLE]; exact hfE) o).resolve_left hf0
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at hge
    by_contra hne
    apply hfnot
    apply mem_rr_single_of_ord o (m := (d : ℤ)) (by rw [← hE, ← hLE]; exact hfE)
    right; omega
  have hclosed : ∀ a ∈ S, ∀ b ∈ S, a + b ≤ d → a + b ∈ S := by
    intro a ha b hb hab
    obtain ⟨-, fa, hfa, hfa0, horda⟩ := (hS_mem a).mp ha
    obtain ⟨-, fb, hfb, hfb0, hordb⟩ := (hS_mem b).mp hb
    rw [hS_mem]; refine ⟨hab, fa * fb, ?_, mul_ne_zero hfa0 hfb0, by rw [Place.ord_mul _ hfa0 hfb0, horda, hordb]; push_cast; ring⟩
    have hprod : fa * fb ∈ riemannRochSpace (((d : ℤ) + d) • Finsupp.single o 1) := by
      rw [add_smul]; rw [hLE, hE] at hfa hfb; exact mul_mem_rr hfa hfb
    rw [hLE, hE]
    apply mem_rr_single_of_ord o hprod
    right; rw [Place.ord_mul _ hfa0 hfb0, horda, hordb]; push_cast; omega

  have hcount := finrank_eq_card_realised o hrat hπ hbot V (2 * d) (by rw [← h2E]; exact hVle)
  have hbig : S ∪ Finset.Ioc d (2 * d) ⊆ (Finset.range (2 * d + 1)).filter (fun j : ℕ => Realised V o j) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range]
    rcases Finset.mem_union.mp hj with hjS | hjI
    · obtain ⟨hjd, f, hf, hf0, hordf⟩ := (hS_mem j).mp hjS
      refine ⟨by omega, f * 1, ?_, by rw [mul_one]; exact hf0, by rw [mul_one, hordf]⟩
      have h1LE : (1 : ↥(modularFunctionFieldBar N)) ∈ LE := by
        obtain ⟨-, one, h1, h10, hord1⟩ := (hS_mem 0).mp h0S
        rw [hLE, mem_riemannRochSpace_iff]; intro w; right
        rw [Place.ord_one]; simp only [hE, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]; split_ifs <;> simp
      rw [hVdef]; exact mul_mem_mul hf h1LE
    · rw [Finset.mem_Ioc] at hjI
      obtain ⟨a, ha, b, hb, habj⟩ := comb g d hd S hS_le h0S hdS hScard hclosed j hjI.1 hjI.2
      obtain ⟨-, fa, hfa, hfa0, horda⟩ := (hS_mem a).mp ha
      obtain ⟨-, fb, hfb, hfb0, hordb⟩ := (hS_mem b).mp hb
      refine ⟨by omega, fa * fb, by rw [hVdef]; exact mul_mem_mul hfa hfb, mul_ne_zero hfa0 hfb0, ?_⟩
      rw [Place.ord_mul _ hfa0 hfb0, horda, hordb, ← habj]; push_cast; ring
  have hdisj : Disjoint S (Finset.Ioc d (2 * d)) := by
    rw [Finset.disjoint_left]; intro j hjS hjI
    have := hS_le j hjS; rw [Finset.mem_Ioc] at hjI; omega
  have hVdim : Module.finrank (AlgebraicClosure ℚ) ↥L2 ≤ Module.finrank (AlgebraicClosure ℚ) ↥V := by
    have h1 := Finset.card_le_card hbig
    rw [Finset.card_union_of_disjoint hdisj, hScard, Nat.card_Ioc, ← hcount] at h1
    have h2 := hfinrank (2 * d) (by omega)
    rw [← h2E, ← hL2] at h2
    have : (Module.finrank (AlgebraicClosure ℚ) ↥L2 : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ) ↥V := by
      rw [h2]; push_cast; omega
    exact_mod_cast this
  exact Submodule.eq_of_le_of_finrank_le hVle hVdim

end Bar

end P2MK1

open AlgebraicCurve ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N] :
    AlgebraicCurve.riemannRochSpace (ModularCurve.embDivisor N)
        * AlgebraicCurve.riemannRochSpace (ModularCurve.embDivisor N)
      = AlgebraicCurve.riemannRochSpace ((2 : ℤ) • ModularCurve.embDivisor N) :=
  P2MK1.main N

end S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
end P2MW
export P2MW.S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self (solution)
