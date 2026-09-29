-- Prove2me | solution 1 for ModularCurve.heckeOperatorBar_self_add_atkinLehner_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/ee875e52-8680-52b4-b956-0a4d7b1bd979

import Mathlib
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_heckeDivBar_self_add_atkinLehner_smul
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_degeneracyPullbackInputs_of_prime
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs_of_prime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

noncomputable section

namespace UpIdentity

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F']

def pullbackAlongHom' (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) : Pic0 K F →+ Pic0 K F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : FundamentalIdentity K F F' := hFI
  Pic0.pullbackHom F'

theorem pullbackAlongHom'_mk (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor.degZero (K := K) (F := F)) :
    pullbackAlongHom' φ hφ hFI (Pic0.mk D) =
      Pic0.mk ⟨Divisor.pullbackAlong φ hφ D, by
        letI := algebraAlong φ
        haveI := isScalarTower_along φ
        haveI := isIntegral_along φ hφ
        haveI : FundamentalIdentity K F F' := hFI
        exact (Pic0.pullbackDegZeroHom F' D).2⟩ :=
  rfl

end UpIdentity

end

open UpIdentity in
theorem solution (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) (x : JZero (N₀ * p)) :
    heckeOperatorBar (N₀ * p) ⟨p, hp⟩ x
        + (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)) • x =
      degeneracyPullbackPair N₀ p 1 (degeneracyPushforwardPair N₀ p 0 x) := by
  haveI : Fact p.Prime := ⟨hp⟩

  obtain ⟨hα', hβ', hP', hfinα', hFI', hNα'⟩ := heckeInputsAlong_of_prime (AlgebraicClosure ℚ) (N₀ * p) p
  haveI := hP'
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N₀ * p)
  have hpull : DegeneracyPullbackInputs N₀ p := degeneracyPullbackInputs_of_prime N₀ p hp
  obtain ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩ := degeneracyPushforwardInputs_of_prime N₀ p

  have eU : ∀ z : JZero (N₀ * p), heckeOperatorBar (N₀ * p) ⟨p, hp⟩ z = heckePic0Bar hα' hβ' hFI' hfinα' hNα' z :=
    fun z => by
      rw [heckeOperatorBar_apply]
      exact DFunLike.congr_fun (heckeOperatorAlong_eq hα' hβ' hFI' hfinα' hNα') z

  have eα : degeneracyPushforwardPair N₀ p 0 =
      Pic0.pushforwardAlongHom (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p) hα hfinα hNα := by
    rw [degeneracyPushforwardPair_eq hα hβ hfinα hNα hfinβ hNβ, Matrix.cons_val_zero]
  have eδ : degeneracyPullbackPair N₀ p 1 =
      pullbackAlongHom' (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hpull.snd.fst hpull.snd.snd.snd.2 := by
    rw [degeneracyPullbackPair, dif_pos hpull]
    simp only [Matrix.cons_val_one]
    rfl
  rw [eU, eα, eδ]

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [heckePic0Bar, Pic0.correspondence_mk, Pic0.smul_mk, ← Pic0.mk_add, Pic0.pushforwardAlongHom_mk,
    pullbackAlongHom'_mk]
  congr 1
  apply Subtype.ext
  exact heckeDivBar_self_add_atkinLehner_smul N₀ p hpN₀ hα' hβ' hα hβ D

end S_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul
end P2MW
export P2MW.S_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul (solution)
