-- Prove2me | solution 1 for ModularCurve.atkinLehner_qExpand_pin_of_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5062c062-13d1-52f1-86f7-046e600db9d4

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHHeckeOperator
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar
import Theorems.Thm_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_atkinLehner_qExpand_pin_of_pin
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve CohCarrier CongruenceSubgroup
open scoped MatrixGroups

namespace AL2Pin

theorem gamma0_le_gamma0_of_dvd {M N : ℕ} (h : N ∣ M) : Gamma0 M ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have : ((A 1 0 : ℤ) : ZMod N) = ZMod.castHom h (ZMod N) ((A 1 0 : ℤ) : ZMod M) := by simp
  rw [this, hA, map_zero]

theorem unitsMap_gamma0Units {M N : ℕ} [NeZero M] [NeZero N] (h : N ∣ M) (A : SL(2, ℤ)) (hA : A ∈ Gamma0 M) :
    ZMod.unitsMap h (gamma0Units M ⟨A, hA⟩) = gamma0Units N ⟨A, gamma0_le_gamma0_of_dvd h hA⟩ := by
  apply Units.ext
  rw [ZMod.unitsMap_def, Units.coe_map, val_gamma0Units, val_gamma0Units]
  show ZMod.castHom h (ZMod N) (Gamma0Map M ⟨A, hA⟩) = Gamma0Map N ⟨A, _⟩
  simp [Gamma0Map]

theorem gammaH_infSubgroup_inf_gamma0_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 M = GammaH M H := by
  ext A
  rw [Subgroup.mem_inf, mem_GammaH_iff, mem_GammaH_iff]
  constructor
  · rintro ⟨⟨hA', hu'⟩, hA⟩
    refine ⟨hA, ?_⟩

    rw [infSubgroup, Subgroup.mem_map] at hu'
    obtain ⟨h, hh, hhu⟩ := hu'
    have hproof : gamma0_le_gamma0_of_dvd (Nat.div_dvd_of_dvd hpM) hA = hA' := rfl
    have key : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (gamma0Units M ⟨A, hA⟩ * h⁻¹) = 1 := by
      rw [map_mul, map_inv, unitsMap_gamma0Units (Nat.div_dvd_of_dvd hpM) A hA, ← hhu, mul_inv_cancel]
    have hmem := hHp _ key
    have : gamma0Units M ⟨A, hA⟩ = gamma0Units M ⟨A, hA⟩ * h⁻¹ * h := by rw [inv_mul_cancel_right]
    rw [this]
    exact H.mul_mem hmem hh
  · rintro ⟨hA, hu⟩
    refine ⟨⟨gamma0_le_gamma0_of_dvd (Nat.div_dvd_of_dvd hpM) hA, ?_⟩, hA⟩
    rw [infSubgroup, Subgroup.mem_map]
    exact ⟨_, hu, unitsMap_gamma0Units (Nat.div_dvd_of_dvd hpM) A hA⟩

end AL2Pin

open ModularCurve

namespace AL2Pin

theorem pin_of_pin_aux
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero p]
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)) = E)
    (h0 : HeckeBetaHDefined (M / p) (infSubgroup p M H hpM) p)
    (c₀ : (ZMod (M / p))ˣ)
    (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ] ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p))))
    (hw1 : ∀ x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), w (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p x) =
      heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p x)
    (hw2 : ∀ x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), w (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p x) =
      heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p (diamondAutHBar (M / p) (infSubgroup p M H hpM) c₀ x))
    (θ : ↥E ≃ₐ[AlgebraicClosure ℚ] ↥E)
    (hθ : ∀ (f : ↥E) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (deck : ∀ τ : ↥E ≃ₐ[AlgebraicClosure ℚ] ↥E,
      (∀ (f : ↥E) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) → ((τ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) → τ = AlgEquiv.refl) :
    ∀ (f : ↥E) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((θ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c₀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  subst hE

  have hw1' : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((w f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu
    have hf : f = heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p u :=
      Subtype.ext (by rw [hfu, coe_heckeAlphaHBar])
    rw [hf, hw1, coe_heckeBetaHBar _ _ _ h0]
  have hw2' : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((w f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c₀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu
    have hf : f = heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p u :=
      Subtype.ext (by rw [hfu, coe_heckeBetaHBar _ _ _ h0])
    rw [hf, hw2, coe_heckeAlphaHBar]

  have hτ : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      (((θ.trans w.symm) f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro f u hfu
    have heq : θ f = w f := Subtype.ext (by rw [hθ f u hfu, hw1' f u hfu])
    show ((w.symm (θ f) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [heq, AlgEquiv.symm_apply_apply, hfu]
  have hdeck := deck (θ.trans w.symm) hτ
  intro f u hfu
  have h1 : w.symm (θ f) = f := DFunLike.congr_fun hdeck f
  have h2 := congrArg w h1
  rw [AlgEquiv.apply_symm_apply] at h2
  rw [h2]
  exact hw2' f u hfu

end AL2Pin

open ModularCurve CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : HeckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hMp : M / p * p = M := Nat.div_mul_cancel hpM
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    rw [pow_two, ← hMp]
    exact Nat.mul_dvd_mul h dvd_rfl |>.trans (by rw [Nat.mul_comm])

  set H' := infSubgroup p M H hpM with hH'

  obtain ⟨w, hw1, hw2⟩ :=
    ModularCurve.exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar (M / p) H' (ℓ := p) hpN hin

  have hΓ : GammaH (M / p) H' ⊓ Gamma0 (M / p * p) = GammaH M H := by
    rw [hMp]; exact AL2Pin.gammaH_infSubgroup_inf_gamma0_eq p M H hpM hHp
  have hT : xHTopFunctionFieldC ℚ (M / p) H' (M / p * p) = xHFunctionField M H := by
    show qExpFunctionFieldC ℚ (GammaH (M / p) H' ⊓ Gamma0 (M / p * p)) = qExpFunctionFieldC ℚ (GammaH M H)
    rw [hΓ]
  have hTB : laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) H' (M / p * p)) =
      xHFunctionFieldBar M H := by
    rw [hT]
  have h0 : HeckeBetaHDefined (M / p) H' p := (hin.heckeInputsHAlong p Fact.out).betaHDefined
  intro c hc f u hfu
  have hcc : c = ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN) := by
    apply Units.ext; rw [hc, ZMod.coe_unitOfCoprime]
  rw [hcc]
  exact AL2Pin.pin_of_pin_aux p M H hpM (xHFunctionFieldBar M H) hTB h0 _ w hw1 hw2 θ hθ
    (fun τ hτ => ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup p M H hpM hpM2 hHp τ hτ) f u hfu

end S_ModularCurve_atkinLehner_qExpand_pin_of_pin
end P2MW
export P2MW.S_ModularCurve_atkinLehner_qExpand_pin_of_pin (solution)
