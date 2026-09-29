-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/84f2d7f4-16e5-50a7-903b-c8364f7959b4

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel"

noncomputable section

namespace E4dictFin

section Regular

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRegularAt_smul_of_mem (v : Place K F) {c : F} (hc : c ∈ v.toValuationSubring) {ω : Ω[F⁄K]}
    (hω : v.IsRegularAt ω) : v.IsRegularAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  exact ⟨c * f, mul_mem hc hf, by rw [smul_smul]⟩

theorem isRegularAt_sum (v : Place K F) {ι : Type*} (s : Finset ι) (ω : ι → Ω[F⁄K])
    (h : ∀ i ∈ s, v.IsRegularAt (ω i)) : v.IsRegularAt (∑ i ∈ s, ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact v.isRegularAt_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem isRegularAt_D_of_mem [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) {d : F} (hd : d ∈ v.toValuationSubring) : v.IsRegularAt (KaehlerDifferential.D K F d) := by
  haveI : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have key : ∀ u : v.toValuationSubring, IsUnit u → v.IsRegularAt (KaehlerDifferential.D K F (u : F)) := by
    intro u hunit
    obtain ⟨w, rfl⟩ := hunit
    have hu0 : ((w : v.toValuationSubring) : F) ≠ 0 := by
      intro h0
      have : (w : v.toValuationSubring) = 0 := Subtype.ext h0
      exact not_isUnit_zero (this ▸ w.isUnit)
    have hord : v.ord ((w : v.toValuationSubring) : F) = 0 := v.ord_coe_unit w
    rcases localUnitDerivativeRegular_of_isCurveOver v _ hu0 hord with h0 | hnn
    · refine ⟨0, zero_mem _, ?_⟩
      rw [zero_smul, ← v.differentialCoeff_smul_dCoord (KaehlerDifferential.D K F _), h0, zero_smul]
    · exact ⟨_, mem_of_ord_nonneg v hnn, (v.differentialCoeff_smul_dCoord _).symm⟩
  by_cases hunit : IsUnit (⟨d, hd⟩ : v.toValuationSubring)
  · exact key ⟨d, hd⟩ hunit
  · have h1 : IsUnit (1 + ⟨d, hd⟩ : v.toValuationSubring) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (1 + ⟨d, hd⟩ : v.toValuationSubring) with h | h
      · exact h
      · exfalso
        apply hunit
        have e : (1 : v.toValuationSubring) - (1 + ⟨d, hd⟩) = -⟨d, hd⟩ := by ring
        rw [e, IsUnit.neg_iff] at h
        exact h
    have h2 := key _ h1
    have e2 : (((1 + ⟨d, hd⟩ : v.toValuationSubring)) : F) = 1 + d := rfl
    rwa [e2, map_add, Derivation.map_one_eq_zero, zero_add] at h2

end Regular

section Series

theorem algebraMap_R_injective (p : ℕ) : Function.Injective (algebraMap (R p) ℚ) := Subtype.val_injective

theorem coeffMap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_qEuler {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : LaurentSeries A) :
    coeffMap φ (qEuler A x) = qEuler B (coeffMap φ x) := by
  ext n
  simp [coeffMap_coeff, qEuler_coeff]

theorem map_map_intCast {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (P : PowerSeries ℤ) :
    (P.map (Int.castRingHom A)).map φ = P.map (Int.castRingHom B) := by
  have h := congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom A) φ)) P
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  rw [← h, RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

end Series

end E4dictFin

open E4dictFin in

theorem solution (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (W₀ : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hW₀ : (∀ f₀ : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (η : (@KaehlerDifferential ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))) (g : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hg : g ∈ W₀)
    (hη : η = g • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (ModularCurve.XHDRLevel.jAt (ModularCurve.XHDRLevel.ΓM M H) hj))
    (P : PowerSeries ℤ)
    (hΘ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) η =
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)))
    (xbar : (𝔛.Mfib A hA ρ hρ).C) (hxbar : xbar ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (𝔭 : PrimeSpectrum ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (h𝔭x : (ModularCurve.XHDRLevel.ιFin p (ModularCurve.XHDRLevel.ΓM M H) hj).base 𝔭 = ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ CategoryTheory.Limits.pullback.fst _ _).base xbar))
    (s : ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj)) (hs : s ∉ 𝔭.asIdeal) (n k : ℕ) (a b : Fin k → ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (hreg : ((s : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) ^ n) • η = ∑ i, ((a i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))) • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (b i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM))⁄(IsLocalRing.ResidueField ↥A)])
    (hω : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM)) ω =
      ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) P) :
    ((𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨xbar, hxbar⟩).IsRegularAt ω := by
  classical

  let κ := IsLocalRing.ResidueField ↥A
  let toκ : R p →+* κ := (IsLocalRing.residue ↥A).comp ρ
  let O := ↥(chartAlgFin p (ΓM M H) hj)
  let F := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let Fb := ↥(qExpFunctionFieldC κ (ΓN p M H hpM))
  let Mf := 𝔛.Mfib A hA ρ hρ
  let g : Mf.C ⟶ X p (ΓM M H) hj := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫
    pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))
  let V : (X p (ΓM M H) hj).Opens := (ιFin p (ΓM M H) hj) ''ᵁ ⊤
  let sec : O → Γ(X p (ΓM M H) hj, V) := fun c =>
    ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of O)).inv c)
  let v : Place κ Fb := Mf.placeOfPoint ⟨xbar, hxbar⟩
  have hgx : g.base xbar = (ιFin p (ΓM M H) hj).base 𝔭 := h𝔭x.symm

  have hxU : xbar ∈ g ⁻¹ᵁ V := by
    show g.base xbar ∈ (V : Set (X p (ΓM M H) hj))
    rw [hgx]
    exact ⟨𝔭, trivial, rfl⟩
  haveI hne : Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ V)) := ⟨⟨xbar, hxU⟩⟩

  let r0 : O →+* Fb :=
    Mf.ffEquiv.symm.toRingHom.comp ((Mf.C.germToFunctionField (g ⁻¹ᵁ V)).hom.comp
      ((g.app V).hom.comp ((((ιFin p (ΓM M H) hj).appIso ⊤).inv.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))))
  have hr0 : ∀ c : O, r0 c = Mf.ffEquiv.symm (Mf.C.germToFunctionField (g ⁻¹ᵁ V) ((g.app V).hom (sec c))) :=
    fun c => rfl

  have hread : ∀ (c : O) (y : LaurentSeries (R p)), coeffMap (algebraMap (R p) ℚ) y = ((c : F) : LaurentSeries ℚ) →
      ((r0 c : Fb) : LaurentSeries κ) = coeffMap toκ y := by
    intro c y hy
    obtain ⟨_, h⟩ :=
      ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_comp_zero_iotaFin_eq_coeffMap_of_mfib
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ c
    exact h y hy

  have hgermff : ∀ t : Γ(Mf.C, g ⁻¹ᵁ V), Mf.C.germToFunctionField (g ⁻¹ᵁ V) t =
      algebraMap (Mf.C.presheaf.stalk xbar) Mf.C.functionField (Mf.C.presheaf.germ (g ⁻¹ᵁ V) xbar hxU t) := by
    intro t
    change _ = (Mf.C.presheaf.stalkSpecializes (genericPoint_specializes xbar)).hom
      ((Mf.C.presheaf.germ (g ⁻¹ᵁ V) xbar hxU).hom t)
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  let φ : Mf.C.presheaf.stalk xbar →+* Fb :=
    Mf.ffEquiv.symm.toRingHom.comp (algebraMap (Mf.C.presheaf.stalk xbar) Mf.C.functionField)
  have hφ : ∀ z, φ z ∈ v.toValuationSubring := by
    intro z
    have hz : φ z ∈ (φ.range : Subring Fb) := ⟨z, rfl⟩
    have hr := Mf.range_stalk_eq ⟨xbar, hxbar⟩
    rw [show φ.range = _ from hr] at hz
    exact hz
  have hr0φ : ∀ c : O, (r0 c : Fb) = φ (Mf.C.presheaf.germ (g ⁻¹ᵁ V) xbar hxU ((g.app V).hom (sec c))) := by
    intro c
    rw [hr0, hgermff]
    rfl
  have hOv : ∀ c : O, (r0 c : Fb) ∈ v.toValuationSubring := fun c => by
    rw [hr0φ]
    exact hφ _

  have hunit : IsUnit (Mf.C.presheaf.germ (g ⁻¹ᵁ V) xbar hxU ((g.app V).hom (sec s))) := by
    have h1 : (ιFin p (ΓM M H) hj).base 𝔭 ∈ (X p (ΓM M H) hj).basicOpen (sec s) := by
      rw [← Scheme.image_basicOpen]
      refine ⟨𝔭, ?_, rfl⟩
      rw [basicOpen_eq_of_affine]
      exact hs
    rw [← hgx] at h1
    have h2 : xbar ∈ g ⁻¹ᵁ ((X p (ΓM M H) hj).basicOpen (sec s)) := h1
    rw [Scheme.preimage_basicOpen] at h2
    exact (Scheme.mem_basicOpen _ _ xbar hxU).mp h2
  obtain ⟨u, hu⟩ := hunit
  have hr0s : (r0 s : Fb) = φ u := by rw [hr0φ, ← hu]
  have hr0s_ne : (r0 s : Fb) ≠ 0 := by
    rw [hr0s]
    exact (u.isUnit.map φ).ne_zero
  have hr0s_inv : (r0 s : Fb)⁻¹ ∈ v.toValuationSubring := by
    have e : (r0 s : Fb)⁻¹ = φ (↑u⁻¹ : Mf.C.presheaf.stalk xbar) := by
      rw [hr0s]
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [e]
    exact hφ _

  obtain ⟨ys, hys⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1 s
  choose ya hya using fun i => (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1 (a i)
  choose yb hyb using fun i => (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).1 (b i)
  have hQ : (((s : F) : LaurentSeries ℚ)) ^ n * HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) =
      ∑ i, ((a i : F) : LaurentSeries ℚ) * qEuler ℚ ((b i : F) : LaurentSeries ℚ) := by
    have e := congrArg (ModularCurve.diffQExp (qExpFunctionFieldC ℚ (ΓM M H))) hreg
    rw [map_smul, map_sum, hΘ] at e
    simp only [map_smul, diffQExp_D] at e
    have e' : ((((s : F) ^ n : F)) : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)) =
        ∑ i, ((a i : F) : LaurentSeries ℚ) * qEuler ℚ ((b i : F) : LaurentSeries ℚ) := e
    rw [← e']
    simp only [SubmonoidClass.coe_pow]
  have hRid : ys ^ n * HahnSeries.ofPowerSeries ℤ (R p) (P.map (Int.castRingHom (R p))) =
      ∑ i, ya i * qEuler (R p) (yb i) := by
    apply E4dictFin.coeffMap_injective (algebraMap (R p) ℚ) (E4dictFin.algebraMap_R_injective p)
    rw [map_mul, map_pow, hys, coeffMap_ofPowerSeries, E4dictFin.map_map_intCast, hQ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, E4dictFin.coeffMap_qEuler, hya, hyb]
  have hκid : (((r0 s : Fb) : LaurentSeries κ)) ^ n * intSeriesC κ P =
      ∑ i, ((r0 (a i) : Fb) : LaurentSeries κ) * qEuler κ ((r0 (b i) : Fb) : LaurentSeries κ) := by
    have e := congrArg (coeffMap toκ) hRid
    rw [map_mul, map_pow, coeffMap_ofPowerSeries, E4dictFin.map_map_intCast, map_sum, ← hread s ys hys] at e
    show (((r0 s : Fb) : LaurentSeries κ)) ^ n * HahnSeries.ofPowerSeries ℤ κ (P.map (Int.castRingHom κ)) = _
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, E4dictFin.coeffMap_qEuler, hread (a i) (ya i) (hya i), hread (b i) (yb i) (hyb i)]

  have hsκ : ((r0 s : Fb) : LaurentSeries κ) ≠ 0 := fun h0 => hr0s_ne (Subtype.ext h0)
  have hΘ₀ : ModularCurve.diffQExp (qExpFunctionFieldC κ (ΓN p M H hpM))
      (∑ i, ((r0 (a i) : Fb) * ((r0 s : Fb)⁻¹) ^ n) • KaehlerDifferential.D κ Fb (r0 (b i) : Fb)) = intSeriesC κ P := by
    rw [map_sum]
    have e2 : ∀ i, ModularCurve.diffQExp (qExpFunctionFieldC κ (ΓN p M H hpM))
        (((r0 (a i) : Fb) * ((r0 s : Fb)⁻¹) ^ n) • KaehlerDifferential.D κ Fb (r0 (b i) : Fb)) =
        ((((r0 s : Fb)⁻¹ : Fb)) : LaurentSeries κ) ^ n *
          (((r0 (a i) : Fb) : LaurentSeries κ) * qEuler κ ((r0 (b i) : Fb) : LaurentSeries κ)) := by
      intro i
      rw [diffQExp_smul_D, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      ring
    have e3 : ((((r0 s : Fb)⁻¹ : Fb)) : LaurentSeries κ) = (((r0 s : Fb) : LaurentSeries κ))⁻¹ := by
      symm
      apply inv_eq_of_mul_eq_one_left
      rw [← MulMemClass.coe_mul, inv_mul_cancel₀ hr0s_ne, OneMemClass.coe_one]
    rw [Finset.sum_congr rfl (fun i _ => e2 i), ← Finset.mul_sum, e3, ← hκid, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hsκ, one_pow, one_mul]

  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne'⟩
  haveI : (ΓN p M H hpM).FiniteIndex := CuspForm.GammaH_finiteIndex (M / p) (infSubgroup p M H hpM)
  have hT' : ModularGroup.T ∈ ΓN p M H hpM := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  have hωeq : ω = ∑ i, ((r0 (a i) : Fb) * ((r0 s : Fb)⁻¹) ^ n) • KaehlerDifferential.D κ Fb (r0 (b i) : Fb) :=
    ModularCurve.diffQExp_qExpFunctionFieldC_injective κ (ΓN p M H hpM) hT' (hω.trans hΘ₀.symm)

  obtain ⟨x, -, htr, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed κ (ΓN p M H hpM) hT'
  haveI := hfd
  haveI : IsCurveOver κ Fb := AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x htr
  haveI : Algebra.EssFiniteType κ Fb := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  rw [hωeq]
  refine E4dictFin.isRegularAt_sum v _ _ fun i _ =>
    E4dictFin.isRegularAt_smul_of_mem v ?_ (E4dictFin.isRegularAt_D_of_mem v (hOv (b i)))
  exact mul_mem (hOv (a i)) (pow_mem hr0s_inv n)

end
end S_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC (solution)
