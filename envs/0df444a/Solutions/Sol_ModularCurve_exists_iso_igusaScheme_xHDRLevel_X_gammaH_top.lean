-- Prove2me | solution 1 for ModularCurve.exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/88250272-6af1-5784-bb6e-e380992604e4

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_of_algEquiv_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve
open scoped MatrixGroups

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ (e : IgusaScheme M p ≅ XHDRLevel.X p (CohCarrier.GammaH M ⊤) hj)
      (eFin : ↥(IgusaScheme.chartAlgFin M p) →+* ↥(XHDRLevel.chartAlgFin p (CohCarrier.GammaH M ⊤) hj))
      (eInf : ↥(IgusaScheme.chartAlgInf M p) →+* ↥(XHDRLevel.chartAlgInf p (CohCarrier.GammaH M ⊤) hj)),

      (∀ x : ↥(IgusaScheme.chartAlgFin M p),
        (((eFin x : ↥(XHDRLevel.chartAlgFin p (CohCarrier.GammaH M ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤))) : LaurentSeries ℚ) =
          ((x : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (∀ x : ↥(IgusaScheme.chartAlgInf M p),
        (((eInf x : ↥(XHDRLevel.chartAlgInf p (CohCarrier.GammaH M ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤))) : LaurentSeries ℚ) =
          ((x : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧

      e.hom ≫ XHDRLevel.toBase p (CohCarrier.GammaH M ⊤) hj = IgusaScheme.igusaTo M p ∧

      Spec.map (CommRingCat.ofHom eFin) ≫ IgusaScheme.ιFin M p = XHDRLevel.ιFin p (CohCarrier.GammaH M ⊤) hj ≫ e.inv ∧
      Spec.map (CommRingCat.ofHom eInf) ≫ IgusaScheme.ιInf M p = XHDRLevel.ιInf p (CohCarrier.GammaH M ⊤) hj ≫ e.inv := by
  haveI : Fact ((IgusaScheme.jFull M : ↥(modularFunctionFieldFull M)) ≠ 0) := IgusaScheme.fact_jFull_ne_zero M

  have hK : modularFunctionFieldFull M = qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤) := by
    rw [CohCarrier.GammaH_top, ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  have hmem : ∀ z : LaurentSeries ℚ, z ∈ modularFunctionFieldFull M ↔ z ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤) := fun z => by rw [hK]
  let ρ : ↥(modularFunctionFieldFull M) ≃+* ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤)) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun y => ⟨y.1, (hmem y.1).mpr y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let σ : ↥(modularFunctionFieldFull M) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤)) :=
    AlgEquiv.ofRingEquiv (f := ρ) (fun r => Subtype.ext rfl)
  have hσ : ∀ x : ↥(modularFunctionFieldFull M), ((σ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) :=
    fun x => rfl
  have hσj : σ (IgusaScheme.jFull M) = XHDRLevel.jAt (CohCarrier.GammaH M ⊤) hj := Subtype.ext rfl

  obtain ⟨w, eFin, eInf, hFin, hInf, hbase, hcFin, hcInf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_of_algEquiv_apply_eq ↥(GaloisRep.ratLocalizedAt p)
      ↥(modularFunctionFieldFull M) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤)) (IgusaScheme.jFull M) (XHDRLevel.jAt (CohCarrier.GammaH M ⊤) hj) σ hσj
  refine ⟨w, eFin.toRingHom, eInf.toRingHom, fun x => ?_, fun x => ?_, hbase, hcFin, hcInf⟩
  · exact (congrArg (fun z : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤)) => (z : LaurentSeries ℚ)) (hFin x)).trans (hσ _)
  · exact (congrArg (fun z : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤)) => (z : LaurentSeries ℚ)) (hInf x)).trans (hσ _)

end S_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
end P2MW
export P2MW.S_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top (solution)
