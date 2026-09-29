-- Prove2me | solution 1 for ModularCurve.exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f94fc591-62c5-551d-a2b6-810e352b0734

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_atkinLehner_qExpand_pin_of_pin
import Theorems.Thm_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
import Theorems.Thm_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand
import Theorems.Thm_ModularCurve_qExpand_mem_xHFunctionField_of_mem_div
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_jqNGen"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace WTComm

theorem norm_exchange {K F T : Type*} [Field K] [Field F] [Field T] [Algebra K F] [Algebra K T]
    (φ : F →ₐ[K] T) (θ : F ≃ₐ[K] F) (Θ : T ≃ₐ[K] T) (hC : ∀ g, Θ (φ g) = φ (θ g)) (y : T) :
    θ (@Algebra.norm F T _ _ (AlgebraicCurve.algebraAlong φ) y) = @Algebra.norm F T _ _ (AlgebraicCurve.algebraAlong φ) (Θ y) := by
  letI := AlgebraicCurve.algebraAlong φ
  have he : RingHom.comp (algebraMap F T) ↑(θ : F ≃+* F) = RingHom.comp ↑(Θ : T ≃+* T) (algebraMap F T) := by
    ext a
    show φ (θ a) = Θ (φ a)
    rw [hC]
  have h := Algebra.norm_eq_of_equiv_equiv (θ : F ≃+* F) (Θ : T ≃+* T) he y
  show θ (Algebra.norm F y) = Algebra.norm F (Θ y)
  rw [h]
  exact (θ : F ≃+* F).apply_symm_apply _

open scoped MatrixGroups in

theorem gammaH_le_gammaH_map {N d : ℕ} (hd : d ∣ N) (K : Subgroup (ZMod N)ˣ) :
    CohCarrier.GammaH N K ≤ CohCarrier.GammaH d (K.map (ZMod.unitsMap hd)) := by
  intro A hA
  obtain ⟨hA0, hAK⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hA0' : A ∈ CongruenceSubgroup.Gamma0 d := by
    have h := congrArg (ZMod.castHom hd (ZMod d)) (CongruenceSubgroup.Gamma0_mem.mp hA0)
    rw [map_intCast, map_zero] at h
    exact CongruenceSubgroup.Gamma0_mem.mpr h
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', ?_⟩
  refine Subgroup.mem_map.mpr ⟨CohCarrier.gamma0Units N ⟨A, hA0⟩, hAK, ?_⟩
  apply Units.ext
  rw [ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  exact ZMod.cast_intCast hd _

theorem qExpand_algebraMap (L : Type*) [Field L] (n : ℕ) [NeZero n] (a : L) :
    qExpand L n (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a := by
  rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

private theorem _root_.WTComm.coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  ModularCurve.coeffMap_qExpand (algebraMap ℚ L) n x

p2m_export "WTComm" "coeffEmb_qExpand"

theorem qExpFunctionFieldC_infSubgroup_le_top (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) ≤ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := by
  show _ ≤ ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))
  apply ModularCurve.qExpFunctionFieldC_mono ℚ
  rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap M ℓ H]
  exact gammaH_le_gammaH_map (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_left hpM ℓ)) _

theorem qExpand_mem_top_of_mem_infSubgroup (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]
    (y : LaurentSeries ℚ) (hy : y ∈ (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))) :
    ModularCurve.qExpand ℚ p y ∈ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := by
  have hβdef : ModularCurve.HeckeBetaHDefined (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) p :=
    ((ModularCurve.heckeDiamondInputsHAll (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))).heckeInputsHAlong p Fact.out).betaHDefined
  have h1 := hβdef y hy
  have hle : CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
      CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) ⊓ CongruenceSubgroup.Gamma0 (M * ℓ / p * p) := by
    rw [Nat.div_mul_cancel (dvd_mul_of_dvd_left hpM ℓ)]
    refine le_inf ?_ inf_le_right
    rw [CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap M ℓ H]
    exact gammaH_le_gammaH_map (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_left hpM ℓ)) _
  exact ModularCurve.qExpFunctionFieldC_mono ℚ hle h1

theorem roofAut_alphaPin
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]

    (Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (σ₀ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃+* ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hΘ : ∀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
        ((Θ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ))
          = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ))
    (hσα : (∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ)))
    (hσβ : (∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
          ∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
            (f : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ) →
              ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) =
                ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c
                    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
                  LaurentSeries (AlgebraicClosure ℚ)))) :
    ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) (u : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((Θ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
  intro f u h

  have key : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) →
      ∃ hz : z ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))), ((Θ ⟨z, hz⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p z := by
    intro z hz
    rw [ModularCurve.mem_laurentBaseChange_iff] at hz
    induction hz using Subfield.closure_induction with
    | mem w hw =>
        rcases hw with ⟨a, rfl⟩ | ⟨y, hy, rfl⟩
        · refine ⟨IntermediateField.algebraMap_mem _ a, ?_⟩
          change ((Θ (algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) a) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
          rw [AlgEquiv.commutes, qExpand_algebraMap]
          rfl
        · have hyF : y ∈ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := qExpFunctionFieldC_infSubgroup_le_top p M hpM H ℓ hy
          refine ⟨ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hyF, ?_⟩
          refine (hΘ ⟨y, hyF⟩).trans ?_
          rw [hσα ⟨y, hyF⟩ ⟨y, hy⟩ rfl, coeffEmb_qExpand]
    | one =>
        refine ⟨one_mem _, ?_⟩
        change ((Θ 1 : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [map_one, map_one]
        rfl
    | add x y _ _ ihx ihy =>
        obtain ⟨hxF, ex⟩ := ihx
        obtain ⟨hyF, ey⟩ := ihy
        refine ⟨add_mem hxF hyF, ?_⟩
        change ((Θ (⟨x, hxF⟩ + ⟨y, hyF⟩) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [map_add, IntermediateField.coe_add, ex, ey, map_add]
    | neg x _ ihx =>
        obtain ⟨hxF, ex⟩ := ihx
        refine ⟨neg_mem hxF, ?_⟩
        change ((Θ (-⟨x, hxF⟩) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [map_neg, IntermediateField.coe_neg, ex, map_neg]
    | inv x _ ihx =>
        obtain ⟨hxF, ex⟩ := ihx
        refine ⟨inv_mem hxF, ?_⟩
        change ((Θ (⟨x, hxF⟩⁻¹) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [map_inv₀, IntermediateField.coe_inv, ex, map_inv₀]
    | mul x y _ _ ihx ihy =>
        obtain ⟨hxF, ex⟩ := ihx
        obtain ⟨hyF, ey⟩ := ihy
        refine ⟨mul_mem hxF hyF, ?_⟩
        change ((Θ (⟨x, hxF⟩ * ⟨y, hyF⟩) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [map_mul, IntermediateField.coe_mul, ex, ey, map_mul]
  obtain ⟨w, hwF⟩ := f
  obtain ⟨z, hzU⟩ := u
  change w = z at h
  subst h
  obtain ⟨_, e⟩ := key w hzU
  exact e

theorem roofAut_betaPin
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]

    (Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (σ₀ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃+* ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hΘ : ∀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
        ((Θ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ))
          = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ))
    (hσα : (∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ)))
    (hσβ : (∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
          ∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
            (f : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ) →
              ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) =
                ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c
                    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
                  LaurentSeries (AlgebraicClosure ℚ)))) :
    ∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
      ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) (u : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((Θ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c u : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
            LaurentSeries (AlgebraicClosure ℚ)) := by
  intro c hc f u h
  have key : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) →
      ∃ (hzU : z ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) (hzF : qExpand (AlgebraicClosure ℚ) p z ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))),
        ((Θ ⟨qExpand (AlgebraicClosure ℚ) p z, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c ⟨z, hzU⟩ : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro z hz
    rw [ModularCurve.mem_laurentBaseChange_iff] at hz
    induction hz using Subfield.closure_induction with
    | mem w hw =>
        rcases hw with ⟨a, rfl⟩ | ⟨y, hy, rfl⟩
        · have hzU : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) := IntermediateField.algebraMap_mem _ a
          have hzF : qExpand (AlgebraicClosure ℚ) p (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a) ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by
            rw [qExpand_algebraMap]; exact IntermediateField.algebraMap_mem _ a
          refine ⟨hzU, hzF, ?_⟩
          have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) a := Subtype.ext (qExpand_algebraMap _ p a)
          have e2 : (⟨_, hzU⟩ : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) a := rfl
          rw [e1, e2, AlgEquiv.commutes, AlgEquiv.commutes]
          rfl
        · have hzU : coeffEmb (AlgebraicClosure ℚ) y ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) := ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy
          have hyβ : ModularCurve.qExpand ℚ p y ∈ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := qExpand_mem_top_of_mem_infSubgroup p M hpM H ℓ y hy
          have hzF : qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) y) ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by
            rw [← coeffEmb_qExpand]; exact ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hyβ
          refine ⟨hzU, hzF, ?_⟩
          have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) =
              ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((⟨ModularCurve.qExpand ℚ p y, hyβ⟩ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ),
                ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (⟨ModularCurve.qExpand ℚ p y, hyβ⟩ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))).2⟩ :=
            Subtype.ext (coeffEmb_qExpand _ p y).symm
          rw [e1, hΘ ⟨ModularCurve.qExpand ℚ p y, hyβ⟩, hσβ c hc ⟨ModularCurve.qExpand ℚ p y, hyβ⟩ ⟨y, hy⟩ rfl]
    | one =>
        have hzF : qExpand (AlgebraicClosure ℚ) p 1 ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by rw [map_one]; exact one_mem _
        refine ⟨one_mem _, hzF, ?_⟩
        have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = 1 := Subtype.ext (map_one _)
        rw [e1, map_one]
        change (1 : LaurentSeries (AlgebraicClosure ℚ)) = ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c 1 : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) : LaurentSeries (AlgebraicClosure ℚ))
        rw [map_one]
        rfl
    | add x y _ _ ihx ihy =>
        obtain ⟨hxU, hxF, ex⟩ := ihx
        obtain ⟨hyU, hyF, ey⟩ := ihy
        have hzF : qExpand (AlgebraicClosure ℚ) p (x + y) ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by rw [map_add]; exact add_mem hxF hyF
        refine ⟨add_mem hxU hyU, hzF, ?_⟩
        have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = ⟨_, hxF⟩ + ⟨_, hyF⟩ := Subtype.ext (map_add _ _ _)
        rw [e1, map_add, IntermediateField.coe_add, ex, ey, ← IntermediateField.coe_add, ← map_add]
        rfl
    | neg x _ ihx =>
        obtain ⟨hxU, hxF, ex⟩ := ihx
        have hzF : qExpand (AlgebraicClosure ℚ) p (-x) ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by rw [map_neg]; exact neg_mem hxF
        refine ⟨neg_mem hxU, hzF, ?_⟩
        have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = -⟨_, hxF⟩ := Subtype.ext (map_neg _ _)
        rw [e1, map_neg, IntermediateField.coe_neg, ex, ← IntermediateField.coe_neg, ← map_neg]
        rfl
    | inv x _ ihx =>
        obtain ⟨hxU, hxF, ex⟩ := ihx
        have hzF : qExpand (AlgebraicClosure ℚ) p x⁻¹ ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by rw [map_inv₀]; exact inv_mem hxF
        refine ⟨inv_mem hxU, hzF, ?_⟩
        have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = ⟨_, hxF⟩⁻¹ := Subtype.ext (map_inv₀ _ _)
        rw [e1, map_inv₀, IntermediateField.coe_inv, ex, ← IntermediateField.coe_inv, ← map_inv₀]
        rfl
    | mul x y _ _ ihx ihy =>
        obtain ⟨hxU, hxF, ex⟩ := ihx
        obtain ⟨hyU, hyF, ey⟩ := ihy
        have hzF : qExpand (AlgebraicClosure ℚ) p (x * y) ∈ (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by rw [map_mul]; exact mul_mem hxF hyF
        refine ⟨mul_mem hxU hyU, hzF, ?_⟩
        have e1 : (⟨_, hzF⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) = ⟨_, hxF⟩ * ⟨_, hyF⟩ := Subtype.ext (map_mul _ _ _)
        rw [e1, map_mul, IntermediateField.coe_mul, ex, ey, ← IntermediateField.coe_mul, ← map_mul]
        rfl
  obtain ⟨w, hwF⟩ := f
  obtain ⟨z, hzU⟩ := u
  change w = qExpand (AlgebraicClosure ℚ) p z at h
  subst h
  obtain ⟨_, _, e⟩ := key z hzU
  exact e

theorem xHFunctionFieldBar_congr_of_eq {T N N' : ℕ} (h : N = N') (hN : N ∣ T) (hN' : N' ∣ T)
    (Ktop : Subgroup (ZMod T)ˣ) :
    xHFunctionFieldBar N (Ktop.map (ZMod.unitsMap hN)) = xHFunctionFieldBar N' (Ktop.map (ZMod.unitsMap hN')) := by
  subst h; rfl

theorem coe_diamondAutHBar_congr_of_eq {T N N' : ℕ} (h : N = N') (hN : N ∣ T) (hN' : N' ∣ T)
    (Ktop : Subgroup (ZMod T)ˣ) (dtop : (ZMod T)ˣ)
    (x : ↥(xHFunctionFieldBar N (Ktop.map (ZMod.unitsMap hN)))) (x' : ↥(xHFunctionFieldBar N' (Ktop.map (ZMod.unitsMap hN'))))
    (hxx' : (x : LaurentSeries (AlgebraicClosure ℚ)) = (x' : LaurentSeries (AlgebraicClosure ℚ))) :
    ((diamondAutHBar N (Ktop.map (ZMod.unitsMap hN)) (ZMod.unitsMap hN dtop) x : ↥(xHFunctionFieldBar N (Ktop.map (ZMod.unitsMap hN)))) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((diamondAutHBar N' (Ktop.map (ZMod.unitsMap hN')) (ZMod.unitsMap hN' dtop) x' : ↥(xHFunctionFieldBar N' (Ktop.map (ZMod.unitsMap hN')))) :
        LaurentSeries (AlgebraicClosure ℚ)) := by
  subst h
  have : x = x' := Subtype.ext hxx'
  subst this
  rfl

theorem coe_diamondAutHBar_congr {N : ℕ} (K₁ K₂ : Subgroup (ZMod N)ˣ) (e : K₁ = K₂) (d₁ d₂ : (ZMod N)ˣ) (ed : d₁ = d₂)
    (y₁ : ↥(xHFunctionFieldBar N K₁)) (y₂ : ↥(xHFunctionFieldBar N K₂))
    (hy : (y₁ : LaurentSeries (AlgebraicClosure ℚ)) = (y₂ : LaurentSeries (AlgebraicClosure ℚ))) :
    ((diamondAutHBar N K₁ d₁ y₁ : ↥(xHFunctionFieldBar N K₁)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((diamondAutHBar N K₂ d₂ y₂ : ↥(xHFunctionFieldBar N K₂)) : LaurentSeries (AlgebraicClosure ℚ)) := by
  subst e; subst ed
  have : y₁ = y₂ := Subtype.ext hy
  subst this
  rfl

section
variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

include hpM in
omit [Fact p.Prime] [NeZero M] in

theorem dvd_mulDiv_and_mulDiv_div_eq (hℓ : ℓ.Prime) : ℓ ∣ M * ℓ / p ∧ M * ℓ / p / ℓ = M / p := by
  have h1 : M * ℓ / p = M / p * ℓ := (Nat.div_mul_right_comm hpM ℓ).symm
  refine ⟨⟨M / p, by rw [h1, mul_comm]⟩, ?_⟩
  rw [h1, Nat.mul_div_cancel _ hℓ.pos]

theorem infSubgroup_mulDiv_eq_map [Fact ℓ.Prime] [NeZero (M * ℓ / p)] (hℓn : ℓ ∣ M * ℓ / p) (hdn : M * ℓ / p / ℓ ∣ M * ℓ) :
    infSubgroup ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn = (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn) := by
  unfold ModularCurve.infSubgroup
  first
    | rfl
    | simp only [Subgroup.map_map, ZMod.unitsMap_comp]

omit [Fact p.Prime] in

theorem infSubgroup_eq_map_comap [NeZero ℓ] (hd : M / p ∣ M * ℓ) :
    infSubgroup p M H hpM = (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd) := by
  unfold ModularCurve.infSubgroup
  have hcomp : ZMod.unitsMap hd = (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)).comp (ZMod.unitsMap (dvd_mul_right M ℓ)) :=
    (ZMod.unitsMap_comp _ _).symm
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_comap_eq_self_of_surjective (ZMod.unitsMap_surjective (dvd_mul_right M ℓ))]

end

section
variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
  (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]

include hℓ in
omit [NeZero p] in

theorem coe_diamondAutHBar_mulDiv_eq_of_coe_eq
    (c : (ZMod (M * ℓ / p))ˣ) (hc : (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)))
    (c₀ : (ZMod (M / p))ˣ) (hc₀ : (c₀ : ZMod (M / p)) = (p : ZMod (M / p)))
    (u : ↥(xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))
    (u₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (huu₀ : (u : LaurentSeries (AlgebraicClosure ℚ)) = (u₀ : LaurentSeries (AlgebraicClosure ℚ))) :
    ((diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c u : ↥(xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c₀ u₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  obtain ⟨hℓn, hdiv⟩ := dvd_mulDiv_and_mulDiv_div_eq p M hpM ℓ hℓ
  have hnT : M * ℓ / p ∣ M * ℓ := Nat.div_dvd_of_dvd (dvd_mul_of_dvd_left hpM ℓ)
  have hdn : M * ℓ / p / ℓ ∣ M * ℓ := (Nat.div_dvd_of_dvd hℓn).trans hnT
  have hd : M / p ∣ M * ℓ := (Nat.div_dvd_of_dvd hpM).trans (dvd_mul_right M ℓ)
  have hmn : M / p ∣ M * ℓ / p := ⟨ℓ, (Nat.div_mul_right_comm hpM ℓ).symm⟩
  have hK := infSubgroup_mulDiv_eq_map p M hpM H ℓ hℓn hdn
  have hK' := infSubgroup_eq_map_comap p M hpM H ℓ hd

  obtain ⟨dtop, hdtop⟩ := ZMod.unitsMap_surjective hnT c
  have hdc : ZMod.unitsMap (Nat.div_dvd_of_dvd hℓn) c = ZMod.unitsMap hdn dtop := by
    rw [← hdtop, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  have hdc₀ : ZMod.unitsMap hd dtop = c₀ := by
    apply Units.ext
    rw [hc₀, ZMod.unitsMap_val]
    calc ((dtop : ZMod (M * ℓ)).cast : ZMod (M / p))
        = ZMod.castHom hd (ZMod (M / p)) (dtop : ZMod (M * ℓ)) := (ZMod.castHom_apply _).symm
      _ = ((ZMod.castHom hmn (ZMod (M / p))).comp (ZMod.castHom hnT (ZMod (M * ℓ / p)))) (dtop : ZMod (M * ℓ)) := by
          rw [ZMod.castHom_comp]
      _ = ZMod.castHom hmn (ZMod (M / p)) (((ZMod.unitsMap hnT dtop : (ZMod (M * ℓ / p))ˣ) : ZMod (M * ℓ / p))) := by
          simp only [RingHom.comp_apply, ZMod.castHom_apply, ZMod.unitsMap_val]
      _ = (p : ZMod (M / p)) := by rw [hdtop, hc, map_natCast]

  have hm'' : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)) := by
    rw [← hK']; exact u₀.2
  have hm' : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)) := by
    rw [xHFunctionFieldBar_congr_of_eq hdiv hdn hd]; exact hm''
  have hm : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M * ℓ / p / ℓ) (infSubgroup ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn) := by
    rw [hK]; exact hm'

  have step1 := ModularCurve.coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn c u
    ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm⟩ huu₀
  rw [step1]
  calc _ = ((diamondAutHBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)) (ZMod.unitsMap hdn dtop) ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm'⟩ :
              ↥(xHFunctionFieldBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)))) : LaurentSeries (AlgebraicClosure ℚ)) :=
          coe_diamondAutHBar_congr _ _ hK _ _ hdc _ _ rfl
    _ = ((diamondAutHBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)) (ZMod.unitsMap hd dtop) ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm''⟩ :
              ↥(xHFunctionFieldBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)))) : LaurentSeries (AlgebraicClosure ℚ)) :=
          coe_diamondAutHBar_congr_of_eq hdiv hdn hd _ dtop _ _ rfl
    _ = _ := coe_diamondAutHBar_congr _ _ hK'.symm _ _ hdc₀ _ _ rfl

include hℓ in
omit [NeZero p] in

theorem coe_diamondAutHBar_mulDiv_eq_qExpand_of_coe_eq_qExpand
    (c : (ZMod (M * ℓ / p))ˣ) (hc : (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)))
    (c₀ : (ZMod (M / p))ˣ) (hc₀ : (c₀ : ZMod (M / p)) = (p : ZMod (M / p)))
    (u : ↥(xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))
    (u₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (huu₀ : (u : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) ℓ (u₀ : LaurentSeries (AlgebraicClosure ℚ))) :
    ((diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c u : ↥(xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) ℓ ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c₀ u₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  obtain ⟨hℓn, hdiv⟩ := dvd_mulDiv_and_mulDiv_div_eq p M hpM ℓ hℓ
  have hnT : M * ℓ / p ∣ M * ℓ := Nat.div_dvd_of_dvd (dvd_mul_of_dvd_left hpM ℓ)
  have hdn : M * ℓ / p / ℓ ∣ M * ℓ := (Nat.div_dvd_of_dvd hℓn).trans hnT
  have hd : M / p ∣ M * ℓ := (Nat.div_dvd_of_dvd hpM).trans (dvd_mul_right M ℓ)
  have hmn : M / p ∣ M * ℓ / p := ⟨ℓ, (Nat.div_mul_right_comm hpM ℓ).symm⟩
  have hK := infSubgroup_mulDiv_eq_map p M hpM H ℓ hℓn hdn
  have hK' := infSubgroup_eq_map_comap p M hpM H ℓ hd

  obtain ⟨dtop, hdtop⟩ := ZMod.unitsMap_surjective hnT c
  have hdc : ZMod.unitsMap (Nat.div_dvd_of_dvd hℓn) c = ZMod.unitsMap hdn dtop := by
    rw [← hdtop, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  have hdc₀ : ZMod.unitsMap hd dtop = c₀ := by
    apply Units.ext
    rw [hc₀, ZMod.unitsMap_val]
    calc ((dtop : ZMod (M * ℓ)).cast : ZMod (M / p))
        = ZMod.castHom hd (ZMod (M / p)) (dtop : ZMod (M * ℓ)) := (ZMod.castHom_apply _).symm
      _ = ((ZMod.castHom hmn (ZMod (M / p))).comp (ZMod.castHom hnT (ZMod (M * ℓ / p)))) (dtop : ZMod (M * ℓ)) := by
          rw [ZMod.castHom_comp]
      _ = ZMod.castHom hmn (ZMod (M / p)) (((ZMod.unitsMap hnT dtop : (ZMod (M * ℓ / p))ˣ) : ZMod (M * ℓ / p))) := by
          simp only [RingHom.comp_apply, ZMod.castHom_apply, ZMod.unitsMap_val]
      _ = (p : ZMod (M / p)) := by rw [hdtop, hc, map_natCast]

  have hm'' : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)) := by
    rw [← hK']; exact u₀.2
  have hm' : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)) := by
    rw [xHFunctionFieldBar_congr_of_eq hdiv hdn hd]; exact hm''
  have hm : (u₀ : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M * ℓ / p / ℓ) (infSubgroup ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn) := by
    rw [hK]; exact hm'

  have step1 := ModularCurve.coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn c u
    ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm⟩ huu₀
  rw [step1]
  congr 1
  calc _ = ((diamondAutHBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)) (ZMod.unitsMap hdn dtop) ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm'⟩ :
              ↥(xHFunctionFieldBar (M * ℓ / p / ℓ) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hdn)))) : LaurentSeries (AlgebraicClosure ℚ)) :=
          coe_diamondAutHBar_congr _ _ hK _ _ hdc _ _ rfl
    _ = ((diamondAutHBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)) (ZMod.unitsMap hd dtop) ⟨(u₀ : LaurentSeries (AlgebraicClosure ℚ)), hm''⟩ :
              ↥(xHFunctionFieldBar (M / p) ((H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))).map (ZMod.unitsMap hd)))) : LaurentSeries (AlgebraicClosure ℚ)) :=
          coe_diamondAutHBar_congr_of_eq hdiv hdn hd _ dtop _ _ rfl
    _ = _ := coe_diamondAutHBar_congr _ _ hK'.symm _ _ hdc₀ _ _ rfl

end

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem roofAut_comp_alpha
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]

    (Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (σ₀ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃+* ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hΘ : ∀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
        ((Θ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ))
          = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ))
    (hσα : (∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ)))
    (hσβ : (∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
          ∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
            (f : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ) →
              ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) =
                ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c
                    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
                  LaurentSeries (AlgebraicClosure ℚ)))) :
    ∀ g : ↥(ModularCurve.xHFunctionFieldBar M H), Θ (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ g) = heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ (θ g) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) hp.pos).ne'⟩

  have hpMl2 : ¬ p ^ 2 ∣ M * ℓ := by
    intro h
    have hcop : Nat.Coprime (p ^ 2) ℓ :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp))
    exact hpM2 (hcop.dvd_of_dvd_mul_right h)
  have hcop₀ : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨k, hk⟩
    apply hpM2
    have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    rw [hM, hk, pow_two]
    exact mul_dvd_mul_left p (dvd_mul_right p k)
  have hcop : Nat.Coprime p (M * ℓ / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨k, hk⟩
    apply hpMl2
    have hM : M * ℓ = p * (M * ℓ / p) := (Nat.mul_div_cancel' (dvd_mul_of_dvd_left hpM ℓ)).symm
    rw [hM, hk, pow_two]
    exact mul_dvd_mul_left p (dvd_mul_right p k)
  let c₀ : (ZMod (M / p))ˣ := ZMod.unitOfCoprime p hcop₀
  have hc₀ : (c₀ : ZMod (M / p)) = (p : ZMod (M / p)) := ZMod.coe_unitOfCoprime p hcop₀
  let c : (ZMod (M * ℓ / p))ˣ := ZMod.unitOfCoprime p hcop
  have hc : (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) := ZMod.coe_unitOfCoprime p hcop

  have hin' : ModularCurve.HeckeDiamondInputsHAll (M / p) (ModularCurve.infSubgroup p M H hpM) :=
    ModularCurve.heckeDiamondInputsHAll _ _
  have hθβ := ModularCurve.atkinLehner_qExpand_pin_of_pin p M H hpM hpM2 hHp hin' θ hθ c₀ hc₀
  have hΘα := roofAut_alphaPin p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ
  have hΘβ := roofAut_betaPin p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ c hc

  have hd1 : M / p ∣ M * ℓ / p := ⟨ℓ, by rw [Nat.div_mul_right_comm hpM ℓ]⟩
  have hgrp : CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) ≤ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) := by
    refine (gammaH_le_gammaH_map hd1 _).trans (ModularCurve.GammaH_mono ?_)
    rintro _ ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    refine Subgroup.mem_map.mpr ⟨ZMod.unitsMap (dvd_mul_right M ℓ) w, hw, ?_⟩
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
  have hUU : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) := by
    show ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) _ ≤ _
    rw [ModularCurve.laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC_mono ℚ hgrp hy)

  let φ₁ : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
    (Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))).comp (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
  let φ₂ : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
    (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).comp (θ : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
  let E : IntermediateField (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
    (AlgHom.equalizer φ₁ φ₂).toIntermediateField (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, map_inv₀, hx])
  have hE : ∀ x, x ∈ E ↔ Θ ((heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) x) = (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) (θ x) := fun x => AlgHom.mem_equalizer φ₁ φ₂ x

  have hgen : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) = (ModularCurve.xHFunctionFieldBar M H) :=
    ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar p M H hpM hpM2 hHp
  have hle1 : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ (ModularCurve.xHFunctionFieldBar M H) :=
    calc (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) := le_sup_left
      _ = (ModularCurve.xHFunctionFieldBar M H) := hgen
  have hle2 : (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) ≤ (ModularCurve.xHFunctionFieldBar M H) :=
    calc (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) ≤ (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) := le_sup_right
      _ = (ModularCurve.xHFunctionFieldBar M H) := hgen

  have h1 : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ IntermediateField.lift E := by
    intro x hx
    have hxM : x ∈ (ModularCurve.xHFunctionFieldBar M H) := hle1 hx
    have key : (⟨x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ E := by
      rw [hE]
      apply Subtype.ext
      rw [hΘα ((heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) ⟨x, hxM⟩) ⟨x, hUU hx⟩ (ModularCurve.coe_heckeAlphaHBar (L := (AlgebraicClosure ℚ)) (M := M) (H := H) (ℓ := ℓ) (x := ⟨x, hxM⟩)),
        ModularCurve.coe_heckeAlphaHBar, hθ ⟨x, hxM⟩ ⟨x, hx⟩ rfl]
      try rfl
    exact (IntermediateField.mem_lift (⟨x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H))).mpr key
  have h2 : (IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ))))) ≤ IntermediateField.lift E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxM : qExpand (AlgebraicClosure ℚ) p x ∈ (ModularCurve.xHFunctionFieldBar M H) :=
      hle2 (IntermediateField.subset_adjoin (AlgebraicClosure ℚ) _ ⟨x, hx, rfl⟩)
    have key : (⟨qExpand (AlgebraicClosure ℚ) p x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ E := by
      rw [hE]
      apply Subtype.ext
      rw [hΘβ ((heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) ⟨_, hxM⟩) ⟨x, hUU hx⟩ (ModularCurve.coe_heckeAlphaHBar (L := (AlgebraicClosure ℚ)) (M := M) (H := H) (ℓ := ℓ) (x := ⟨_, hxM⟩)),
        ModularCurve.coe_heckeAlphaHBar, hθβ ⟨_, hxM⟩ ⟨x, hx⟩ rfl]
      exact coe_diamondAutHBar_mulDiv_eq_of_coe_eq p M hpM H ℓ hℓ c hc c₀ hc₀ ⟨x, hUU hx⟩ ⟨x, hx⟩ rfl
    exact (IntermediateField.mem_lift (⟨_, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H))).mpr key

  have hlift : IntermediateField.lift E = (ModularCurve.xHFunctionFieldBar M H) := by
    apply le_antisymm (IntermediateField.lift_le E)
    calc (ModularCurve.xHFunctionFieldBar M H) = _ := hgen.symm
      _ ≤ IntermediateField.lift E := sup_le h1 h2
  have hEtop : E = ⊤ := by
    apply IntermediateField.lift_injective (ModularCurve.xHFunctionFieldBar M H)
    rw [hlift]
    exact (IntermediateField.lift_top (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)).symm
  intro g
  have hg : g ∈ E := by rw [hEtop]; exact IntermediateField.mem_top
  exact (hE g).mp hg

theorem xHFunctionField_congr_of_eq {T N N' : ℕ} (h : N = N') (hN : N ∣ T) (hN' : N' ∣ T)
    (Ktop : Subgroup (ZMod T)ˣ) :
    xHFunctionField N (Ktop.map (ZMod.unitsMap hN)) = xHFunctionField N' (Ktop.map (ZMod.unitsMap hN')) := by
  subst h; rfl

noncomputable def qExpandAlgHom (L : Type*) [Field L] (n : ℕ) [NeZero n] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L n with
    commutes' := fun r => by
      show qExpand L n (algebraMap L (LaurentSeries L) r) = algebraMap L (LaurentSeries L) r
      rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

theorem qExpandAlgHom_apply (L : Type*) [Field L] (n : ℕ) [NeZero n] (x : LaurentSeries L) :
    qExpandAlgHom L n x = qExpand L n x := rfl

section StarC2
variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) (hℓ : ℓ.Prime)
  [NeZero ℓ] [NeZero (M * ℓ / p)]

include hℓ in

theorem qExpand_mem_xHFunctionFieldBar_mulDiv {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    qExpand (AlgebraicClosure ℚ) ℓ x ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  obtain ⟨hℓn, hdiv⟩ := dvd_mulDiv_and_mulDiv_div_eq p M hpM ℓ hℓ
  have hnT : M * ℓ / p ∣ M * ℓ := Nat.div_dvd_of_dvd (dvd_mul_of_dvd_left hpM ℓ)
  have hdn : M * ℓ / p / ℓ ∣ M * ℓ := (Nat.div_dvd_of_dvd hℓn).trans hnT
  have hd : M / p ∣ M * ℓ := (Nat.div_dvd_of_dvd hpM).trans (dvd_mul_right M ℓ)
  have hK := infSubgroup_mulDiv_eq_map p M hpM H ℓ hℓn hdn
  have hK' := infSubgroup_eq_map_comap p M hpM H ℓ hd

  have hrat : ∀ y ∈ xHFunctionField (M / p) (ModularCurve.infSubgroup p M H hpM),
      qExpand ℚ ℓ y ∈ xHFunctionField (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) := by
    intro y hy
    have hy' : y ∈ xHFunctionField (M * ℓ / p / ℓ) (infSubgroup ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn) := by
      rw [hK, xHFunctionField_congr_of_eq hdiv hdn hd, ← hK']; exact hy
    exact ModularCurve.qExpand_mem_xHFunctionField_of_mem_div ℓ (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) hℓn hy'

  have hsub : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ ((ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))).comap (qExpandAlgHom (AlgebraicClosure ℚ) ℓ) := by
    change IntermediateField.adjoin (AlgebraicClosure ℚ) _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    show qExpandAlgHom (AlgebraicClosure ℚ) ℓ (coeffEmb (AlgebraicClosure ℚ) y) ∈ (ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))
    rw [qExpandAlgHom_apply, ← ModularCurve.coeffEmb_qExpand]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hrat y hy)
  exact hsub hx

end StarC2

theorem roofAut_comp_beta
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) [NeZero ℓ] [NeZero p] [NeZero (M * ℓ / p)]

    (Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (σ₀ : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ≃+* ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (hΘ : ∀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
        ((Θ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ))
          = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ y : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ))
    (hσα : (∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ)))
    (hσβ : (∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
          ∀ (f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
            (f : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ) →
              ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ f : ↥(ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries ℚ) =
                ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c
                    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
                  LaurentSeries (AlgebraicClosure ℚ)))) :
    ∀ g : ↥(ModularCurve.xHFunctionFieldBar M H), Θ (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ g) = heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (θ g) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hp : p.Prime := Fact.out
  haveI hMp : NeZero (M / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) hp.pos).ne'⟩

  have hβdef : HeckeBetaHDefined M H ℓ := (hin.heckeInputsHAlong ℓ hℓ).fst
  have hβcoe : ∀ g : ↥(ModularCurve.xHFunctionFieldBar M H), ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ g : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) ℓ (g : LaurentSeries (AlgebraicClosure ℚ)) := fun g => coe_heckeBetaHBar M H ℓ hβdef g

  have hB1 := roofAut_alphaPin p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ
  have hB2 := roofAut_betaPin p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ

  have hcop0 : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨k, hk⟩
    apply hpM2
    rw [(Nat.mul_div_cancel' hpM).symm, hk, pow_two]
    exact mul_dvd_mul_left p (dvd_mul_right p k)
  have hcop : Nat.Coprime p (M * ℓ / p) := by
    rw [(Nat.div_mul_right_comm hpM ℓ).symm]
    exact Nat.Coprime.mul_right hcop0 ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp))
  let c₀ : (ZMod (M / p))ˣ := ZMod.unitOfCoprime p hcop0
  have hc₀ : (c₀ : ZMod (M / p)) = (p : ZMod (M / p)) := ZMod.coe_unitOfCoprime p hcop0
  let c : (ZMod (M * ℓ / p))ˣ := ZMod.unitOfCoprime p hcop
  have hc : (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) := ZMod.coe_unitOfCoprime p hcop

  have hθβ := ModularCurve.atkinLehner_qExpand_pin_of_pin p M H hpM hpM2 hHp
    (ModularCurve.heckeDiamondInputsHAll (M / p) (ModularCurve.infSubgroup p M H hpM)) θ hθ c₀ hc₀

  have hgen : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ)))) = (ModularCurve.xHFunctionFieldBar M H) :=
    ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_eq_xHFunctionFieldBar p M H hpM hpM2 hHp
  have hle1 : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ (ModularCurve.xHFunctionFieldBar M H) :=
    calc (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ)))) := le_sup_left
      _ = (ModularCurve.xHFunctionFieldBar M H) := hgen
  have hle2 : IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ (ModularCurve.xHFunctionFieldBar M H) :=
    calc _ ≤ (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ⊔ IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ)))) := le_sup_right
      _ = (ModularCurve.xHFunctionFieldBar M H) := hgen

  let φ₁ : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := Θ.toAlgHom.comp (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ)
  let φ₂ : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).comp θ.toAlgHom
  let E : IntermediateField (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
    (AlgHom.equalizer φ₁ φ₂).toIntermediateField (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, map_inv₀, hx])
  have hE : ∀ g, g ∈ E ↔ Θ (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ g) = heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (θ g) :=
    fun g => AlgHom.mem_equalizer φ₁ φ₂ g

  have hcomm : ∀ z : LaurentSeries (AlgebraicClosure ℚ), qExpand (AlgebraicClosure ℚ) ℓ (qExpand (AlgebraicClosure ℚ) p z) = qExpand (AlgebraicClosure ℚ) p (qExpand (AlgebraicClosure ℚ) ℓ z) := fun z => by
    rw [ModularCurve.qExpand_qExpand, ModularCurve.qExpand_qExpand, ModularCurve.qExpand_congr (Nat.mul_comm ℓ p)]

  have h1 : (ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) ≤ IntermediateField.lift E := by
    intro x hx
    have hxM : x ∈ (ModularCurve.xHFunctionFieldBar M H) := hle1 hx
    have hxℓ := qExpand_mem_xHFunctionFieldBar_mulDiv p M hpM H ℓ hℓ hx
    have key : (⟨x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ E := by
      rw [hE]
      apply Subtype.ext
      rw [hB1 (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ ⟨x, hxM⟩) ⟨qExpand (AlgebraicClosure ℚ) ℓ x, hxℓ⟩ (hβcoe ⟨x, hxM⟩), hβcoe,
        hθ ⟨x, hxM⟩ ⟨x, hx⟩ rfl]
      exact (hcomm x).symm
    exact (IntermediateField.mem_lift (⟨x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H))).mpr key

  have h2 : IntermediateField.adjoin (AlgebraicClosure ℚ) (⇑(qExpand (AlgebraicClosure ℚ) p) '' ((ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) : Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤ IntermediateField.lift E := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxM : qExpand (AlgebraicClosure ℚ) p x ∈ (ModularCurve.xHFunctionFieldBar M H) := hle2 (IntermediateField.subset_adjoin (AlgebraicClosure ℚ) _ ⟨x, hx, rfl⟩)
    have hxℓ := qExpand_mem_xHFunctionFieldBar_mulDiv p M hpM H ℓ hℓ hx
    have key : (⟨qExpand (AlgebraicClosure ℚ) p x, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ E := by
      rw [hE]
      apply Subtype.ext
      have eβ : ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ ⟨qExpand (AlgebraicClosure ℚ) p x, hxM⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p ((⟨qExpand (AlgebraicClosure ℚ) ℓ x, hxℓ⟩ : ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) := by
        rw [hβcoe]; exact hcomm x
      rw [hB2 c hc _ ⟨qExpand (AlgebraicClosure ℚ) ℓ x, hxℓ⟩ eβ, hβcoe, hθβ _ ⟨x, hx⟩ rfl]
      exact coe_diamondAutHBar_mulDiv_eq_qExpand_of_coe_eq_qExpand p M hpM H ℓ hℓ c hc c₀ hc₀ ⟨qExpand (AlgebraicClosure ℚ) ℓ x, hxℓ⟩ ⟨x, hx⟩ rfl
    exact (IntermediateField.mem_lift (⟨_, hxM⟩ : ↥(ModularCurve.xHFunctionFieldBar M H))).mpr key

  have hlift : IntermediateField.lift E = (ModularCurve.xHFunctionFieldBar M H) := by
    apply le_antisymm (IntermediateField.lift_le E)
    calc (ModularCurve.xHFunctionFieldBar M H) = _ := hgen.symm
      _ ≤ IntermediateField.lift E := sup_le h1 h2
  have hEtop : E = ⊤ := by
    apply IntermediateField.lift_injective (ModularCurve.xHFunctionFieldBar M H)
    rw [hlift]
    exact (IntermediateField.lift_top (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H)).symm
  intro g
  have hg : g ∈ E := by rw [hEtop]; exact IntermediateField.mem_top
  exact (hE g).mp hg

theorem exists_roofAut
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ Θ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))),
      (∀ g : ↥(ModularCurve.xHFunctionFieldBar M H), Θ (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ g) = heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ (θ g)) ∧
      (∀ g : ↥(ModularCurve.xHFunctionFieldBar M H), Θ (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ g) = heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (θ g)) := by
  haveI hℓ0 : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let Ht : Subgroup (ZMod (M * ℓ))ˣ := H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))
  have hroof : CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) = CohCarrier.GammaH (M * ℓ) Ht :=
    CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap M ℓ H
  have hF : ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) = ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ) Ht) := by
    unfold ModularCurve.xHTopFunctionFieldC; rw [hroof]
  have hpMl : p ∣ M * ℓ := dvd_mul_of_dvd_left hpM ℓ
  have hpMl2 : ¬ p ^ 2 ∣ M * ℓ := by
    intro h
    have hcop : Nat.Coprime (p ^ 2) ℓ :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes (Fact.out) hℓ).mpr (Ne.symm hℓp))
    exact hpM2 (hcop.dvd_of_dvd_mul_right h)
  have hHpt : ∀ u : (ZMod (M * ℓ))ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpMl) u = 1 → u ∈ Ht := by
    intro u hu
    show ZMod.unitsMap (dvd_mul_right M ℓ) u ∈ H
    apply hHp

    have hd1 : M / p ∣ M * ℓ / p := ⟨ℓ, by rw [Nat.div_mul_right_comm hpM ℓ]⟩
    have key : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (ZMod.unitsMap (dvd_mul_right M ℓ) u) =
        ZMod.unitsMap hd1 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpMl) u) := by
      rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, ← MonoidHom.comp_apply, ZMod.unitsMap_comp]
    rw [key, hu, map_one]

  haveI : NeZero (M * ℓ / p) := ⟨by rw [← Nat.div_mul_right_comm hpM ℓ]; exact Nat.mul_ne_zero (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos).ne' hℓ.ne_zero⟩
  have main : ∀ (F₀ : IntermediateField ℚ (LaurentSeries ℚ)), F₀ = ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ) Ht) →
      ∃ σ₀ : ↥F₀ ≃+* ↥F₀, (∀ (f : ↥F₀) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ₀ f : ↥F₀) : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ)) ∧ (∀ (c : (ZMod (M * ℓ / p))ˣ), (c : ZMod (M * ℓ / p)) = (p : ZMod (M * ℓ / p)) →
          ∀ (f : ↥F₀) (u : ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ))))),
            (f : LaurentSeries ℚ) = ModularCurve.qExpand ℚ p (u : LaurentSeries ℚ) →
              ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((σ₀ f : ↥F₀) : LaurentSeries ℚ) =
                ((ModularCurve.diamondAutHBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)) c
                    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(ModularCurve.xHFunctionFieldBar (M * ℓ / p) (ModularCurve.infSubgroup p (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) (dvd_mul_of_dvd_left hpM ℓ)))) :
                  LaurentSeries (AlgebraicClosure ℚ))) := by
    intro F₀ hF₀
    subst hF₀
    obtain ⟨σ, h1, h2⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p (M * ℓ) Ht hpMl hpMl2 hHpt
    exact ⟨(σ : _ ≃+* _), fun f u h => h1 f u h, fun c hc f u h => h2 c hc f u h⟩
  obtain ⟨σ₀, hσα, hσβ⟩ := main (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) hF
  obtain ⟨Θ, hΘ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) σ₀
  exact ⟨Θ, roofAut_comp_alpha p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ,
    roofAut_comp_beta p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp Θ σ₀ hΘ hσα hσβ⟩

end WTComm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      SemilinearAut.ofAlgAut θ • (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
          (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ ((SemilinearAut.ofAlgAut θ)⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) c * (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
          (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : ↥(ModularCurve.xHFunctionFieldBar M H))) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨Θ, hC1, hC2⟩ := WTComm.exists_roofAut p M hpM hpM2 H hHp hin θ hθ ℓ hℓ hℓp
  refine ⟨1, one_ne_zero, ?_⟩
  rw [map_one, one_mul]
  have hinv : (SemilinearAut.ofAlgAut θ)⁻¹ • f = θ.symm f := by
    rw [← map_inv, SemilinearAut.ofAlgAut_smul]; rfl
  rw [hinv, SemilinearAut.ofAlgAut_smul]
  show θ (@Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) _ _ (AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (θ.symm f))) = _
  rw [WTComm.norm_exchange (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) θ Θ hC1, hC2, AlgEquiv.apply_symm_apply]

#print axioms solution

end S_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne
end P2MW
export P2MW.S_ModularCurve_exists_ofAlgAut_smul_norm_heckeBetaHBar_inv_smul_eq_algebraMap_mul_norm_heckeBetaHBar_of_ne (solution)
