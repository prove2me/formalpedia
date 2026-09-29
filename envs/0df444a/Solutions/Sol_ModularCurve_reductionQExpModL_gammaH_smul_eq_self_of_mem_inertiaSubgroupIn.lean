-- Prove2me | solution 1 for ModularCurve.reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ff0a2b27-d65b-5e8f-8f6a-df2eaeca6b8a

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsLaurentPlaceReduction laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral LaurentReductionInputs laurentReductionDegZero coe_laurentReductionDegZero laurentReduction laurentReduction_mk IsLaurentPlaceReduction.eq_or_const_of_agree ReductionInputsQExpModL reductionQExpModL qExpFunctionFieldC arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def coeffMap coeffMap_coeffMap coeffMap_congr laurentBaseChange coeffMap_mem_laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH JH JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace QExpInertRed
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn.ModularCurve HahnSeries IntermediateField"
open scoped Pointwise

section Generic

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

abbrev FL (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Type _ :=
  laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

theorem coeffMap_subtype_coeffMap (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (y : LaurentSeries A) :
    coeffMap A.subtype (coeffMap σA y) = coeffMap (σ : L →+* L) (coeffMap A.subtype y) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun a => hσA a) y

theorem mapDomain_inertia_agree
    {r : Place L (FL L Γ) → Place k (qExpFunctionFieldC k Γ)}
    (hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = π a)
    {D : Divisor L (FL L Γ)}
    (hD : D ∈ laurentIntegralPrincipalDivisors A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ)) :
    Finsupp.mapDomain r D =
      Finsupp.mapDomain (r ∘ fun P => arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ • P) D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  set y' : LaurentSeries A := coeffMap σA y with hy'def
  have himg : coeffMap A.subtype y' = coeffMap (σ : L →+* L) (coeffMap A.subtype y) :=
    coeffMap_subtype_coeffMap σ σA hσA y
  have hy' : coeffMap A.subtype y' ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
    rw [himg]; exact coeffMap_mem_laurentBaseChange σ hy

  have hred : coeffMap π y' = coeffMap π y := by
    rw [hy'def, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => hπ a) y
  have hyk' : coeffMap π y' ∈ qExpFunctionFieldC k Γ := hred ▸ hyk
  have hne' : coeffMap π y' ≠ 0 := hred ▸ hne
  have hyeq : (⟨coeffMap π y', hyk'⟩ : qExpFunctionFieldC k Γ) = ⟨coeffMap π y, hyk⟩ := Subtype.ext hred

  have hgx : g • (⟨coeffMap A.subtype y, hy⟩ : FL L Γ) = ⟨coeffMap A.subtype y', hy'⟩ :=
    Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact himg.symm)

  have hD' : ∀ P, (g • D) P = P.ord (⟨coeffMap A.subtype y', hy'⟩ : FL L Γ) := by
    intro P
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hgx, ← SemilinearAut.ord_smul g (g⁻¹ • P), smul_inv_smul]

  rw [Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def]
  ext Q
  rw [hr.2 y hy hyk hne D hDy Q, hr.2 y' hy' hyk' hne' (g • D) hD' Q, hyeq]

theorem mapDomain_eq_zero_of_const {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F']
    [Algebra K' F'] {r : Place K F → Place K' F'} (hconst : ∀ P Q, r P = r Q) (hdeg : ∀ P : Place K F, P.deg = 1)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Finsupp.mapDomain r D = 0 := by
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨P₀⟩⟩
  · have : D = 0 := Finsupp.ext fun P => isEmptyElim P
    rw [this, Finsupp.mapDomain_zero]
  · have hmapconst : ∀ D : Divisor K F, Finsupp.mapDomain r D = Finsupp.single (r P₀) (Divisor.degree D) := by
      intro D
      induction D using Finsupp.induction with
      | zero => simp
      | single_add P n D _ _ ih =>
        rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hconst P P₀, map_add,
          Divisor.degree_single, hdeg, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
    rw [hmapconst D, (Divisor.mem_degZero.mp hD), Finsupp.single_zero]

set_option maxHeartbeats 3200000 in

theorem laurentReduction_smul_eq_self
    (h : LaurentReductionInputs A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ))
    (hdegL : ∀ P : Place L (FL L Γ), P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (FL L Γ), ∃ y : Pic0 L (FL L Γ), n • y = x)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = π a)
    (x : Pic0 L (FL L Γ)) :
    laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) (σ • x) =
      laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) x := by
  set r := h.choose with hrdef
  have hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r := h.choose_spec.1
  have hgen : LaurentPrincipalGeneratedByIntegral A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) :=
    h.choose_spec.2
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk, laurentReduction_mk h, laurentReduction_mk h]

  rcases IsLaurentPlaceReduction.eq_or_const_of_agree (r₁ := r)
      (r₂ := r ∘ fun P => g • P) hgen (fun D hD => mapDomain_inertia_agree hr σ σA hσA hπ hD) hdegL hdiv with
    key | hconst
  · congr 1
    apply Subtype.ext
    rw [coe_laurentReductionDegZero, coe_laurentReductionDegZero, SemilinearAut.coe_degZeroSMulHom,
      SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, ← hg, show h.choose = r from rfl, ← key]
  ·
    have h0 : ∀ E : Divisor.degZero (K := L) (F := FL L Γ),
        laurentReductionDegZero h.choose h.choose_spec.1.1 E = 0 := fun E =>
      Subtype.ext (by rw [coe_laurentReductionDegZero]; exact mapDomain_eq_zero_of_const hconst hdegL E.2)
    rw [h0, h0]

end Generic

section Modular

open ValuationSubring

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem main (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h : ModularCurve.ReductionInputsQExpModL A Γ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)) :
    ModularCurve.reductionQExpModL A Γ (τ • z) = ModularCurve.reductionQExpModL A Γ z := by

  obtain ⟨t, ht, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfd
  have hdegL : ∀ P : Place (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), n • y = x :=
    fun n hn x => AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)
      ⟨t, ht, hfd⟩ n hn x

  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hτ
  let σA : A →+* A := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A s
  have hσA : ∀ a : A, (σA a : AlgebraicClosure ℚ) = (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a :=
    fun a => rfl
  have hs1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (IsLocalRing.ResidueField A) s = 1 :=
    (MonoidHom.mem_ker).mp hs
  have hπ : ∀ a : A, IsLocalRing.residue A (σA a) = IsLocalRing.residue A a := by
    intro a
    show IsLocalRing.residue A (s • a) = _
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := RingEquiv.congr_fun hs1 (IsLocalRing.residue A a)
    simpa using h1
  exact laurentReduction_smul_eq_self h hdegL hdiv (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    σA hσA hπ z

end Modular

end ModularCurve.QExpInertRed

end

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) (τ • z) =
      ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z :=
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  ModularCurve.QExpInertRed.main (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) A h τ hτ z

end S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn (solution)
