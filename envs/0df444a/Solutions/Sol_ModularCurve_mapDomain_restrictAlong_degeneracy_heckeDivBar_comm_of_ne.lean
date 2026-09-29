-- Prove2me | solution 1 for ModularCurve.mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/37335039-3355-566b-a817-852d2d54e97d

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeNamedInputs
import Theorems.Thm_ModularCurve_heckeExchangeAt_of_primes_of_ne
import Theorems.Thm_ModularCurve_heckeBetaExchangeAt_of_primes_of_ne
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne.AlgebraicCurve ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence_apply Divisor.pushforwardAlong_single Place Divisor HasPrincipalDivisors Divisor.pushforwardAlong_pushforwardAlong"
namespace Divisor
p2m_export "AlgebraicCurve.Divisor" "pullbackAlong pushforwardAlong correspondence_apply pushforwardAlong_single degree pushforwardAlong_pushforwardAlong"
p2m_open "AlgebraicCurve.Divisor AlgebraicCurve"
theorem pullbackAlong_congr'' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F'] {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F) :
    pullbackAlong φ hφ D = pullbackAlong φ' hφ' D := by subst h; rfl
theorem pushforwardAlong_congr'' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F') :
    pushforwardAlong φ hφ D = pushforwardAlong φ' hφ' D := by subst h; rfl
end AlgebraicCurve.Divisor

namespace DegComm

theorem inertiaDegAlong_eq_one {N M : ℕ} [NeZero N] [NeZero M]
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (hφ : φ.toRingHom.IsIntegral) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := modularFunctionFieldBar N)
  rw [deg_eq_one_modularFunctionFieldBar M w, deg_eq_one_modularFunctionFieldBar N, one_mul] at h
  exact h

theorem pushforwardAlong_eq_mapDomain {N M : ℕ} [NeZero N] [NeZero M]
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (hφ : φ.toRingHom.IsIntegral) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) :
    Divisor.pushforwardAlong φ hφ D = Finsupp.mapDomain (·.restrictAlong φ hφ) D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, Finsupp.mapDomain_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Divisor.pushforwardAlong_single, ih,
      inertiaDegAlong_eq_one, Nat.cast_one, mul_one]

section Chains

variable (N q : ℕ) [NeZero N] [Fact q.Prime] [NeZero q] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hℓq : ℓ ≠ q)

local notation "𝕃" => AlgebraicClosure ℚ

include hℓq in

theorem alpha_chain
    (hα₀ : (heckeAlphaBar 𝕃 N q).toRingHom.IsIntegral)
    (hα₁ : (heckeAlphaBar 𝕃 (N * q) ℓ).toRingHom.IsIntegral)
    (hβ₁ : (heckeBetaBar 𝕃 (N * q) ℓ).toRingHom.IsIntegral)
    (hα₂ : (heckeAlphaBar 𝕃 N ℓ).toRingHom.IsIntegral)
    (hβ₂ : (heckeBetaBar 𝕃 N ℓ).toRingHom.IsIntegral)
    [HasPrincipalDivisors 𝕃 (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors 𝕃 (modularFunctionFieldBar (N * q * ℓ))]
    (D : Divisor 𝕃 (modularFunctionFieldBar (N * q))) :
    Divisor.pushforwardAlong (heckeAlphaBar 𝕃 N q) hα₀
        (Divisor.pushforwardAlong (heckeAlphaBar 𝕃 (N * q) ℓ) hα₁
          (Divisor.pullbackAlong (heckeBetaBar 𝕃 (N * q) ℓ) hβ₁ D))
      = Divisor.pushforwardAlong (heckeAlphaBar 𝕃 N ℓ) hα₂
          (Divisor.pullbackAlong (heckeBetaBar 𝕃 N ℓ) hβ₂
            (Divisor.pushforwardAlong (heckeAlphaBar 𝕃 N q) hα₀ D)) := by
  have hM : N * q * ℓ = N * ℓ * q := Nat.mul_right_comm N q ℓ
  have hex : HeckeExchangeAt 𝕃 N ℓ q (N * q * ℓ) hM :=
    heckeExchangeAt_of_primes_of_ne 𝕃 N ℓ q (N * q * ℓ) Fact.out Fact.out hℓq hM
  have hu : (towerInclBar 𝕃 (dvd_of_eq_roof N ℓ q _ hM).1).toRingHom.IsIntegral :=
    towerInclBar_isIntegral 𝕃 (dvd_of_eq_roof N ℓ q _ hM).1
  have hu' : (towerSubstBar 𝕃 (N * q) ℓ (dvd_of_eq_roof N ℓ q _ hM).2).toRingHom.IsIntegral :=
    towerSubstBar_isIntegral 𝕃 ℓ (dvd_of_eq_roof N ℓ q _ hM).2
  rw [hex hβ₂ hα₀ hu hu' D]
  have hc₁ : ((heckeAlphaBar 𝕃 (N * q) ℓ).comp (heckeAlphaBar 𝕃 N q)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hα₀ hα₁
  have hc₂ : ((towerInclBar 𝕃 (dvd_of_eq_roof N ℓ q _ hM).1).comp
      (heckeAlphaBar 𝕃 N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hα₂ hu
  rw [Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaBar 𝕃 N q)
        (heckeAlphaBar 𝕃 (N * q) ℓ) hα₀ hα₁ hc₁,
      Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaBar 𝕃 N ℓ)
        (towerInclBar 𝕃 (dvd_of_eq_roof N ℓ q _ hM).1) hα₂ hu hc₂]
  have h0 : N ∣ N * q * ℓ := Dvd.intro (q * ℓ) (Nat.mul_assoc N q ℓ).symm
  have e₁ : (heckeAlphaBar 𝕃 (N * q) ℓ).comp (heckeAlphaBar 𝕃 N q) = towerInclBar 𝕃 h0 :=
    towerInclBar_comp_heckeAlphaBar 𝕃 q (dvd_mul_right (N * q) ℓ) h0
  have e₂ : (towerInclBar 𝕃 (dvd_of_eq_roof N ℓ q _ hM).1).comp (heckeAlphaBar 𝕃 N ℓ)
      = towerInclBar 𝕃 h0 :=
    towerInclBar_comp_heckeAlphaBar 𝕃 ℓ _ h0
  have hI : (towerInclBar 𝕃 h0).toRingHom.IsIntegral := towerInclBar_isIntegral 𝕃 h0
  rw [Divisor.pushforwardAlong_congr'' e₁ hc₁ hI, Divisor.pushforwardAlong_congr'' e₂ hc₂ hI]
  congr 1

include hℓq in

theorem beta_chain
    (hβ₀ : (heckeBetaBar 𝕃 N q).toRingHom.IsIntegral)
    (hα₁ : (heckeAlphaBar 𝕃 (N * q) ℓ).toRingHom.IsIntegral)
    (hβ₁ : (heckeBetaBar 𝕃 (N * q) ℓ).toRingHom.IsIntegral)
    (hα₂ : (heckeAlphaBar 𝕃 N ℓ).toRingHom.IsIntegral)
    (hβ₂ : (heckeBetaBar 𝕃 N ℓ).toRingHom.IsIntegral)
    [HasPrincipalDivisors 𝕃 (modularFunctionFieldBar (N * ℓ))]
    [HasPrincipalDivisors 𝕃 (modularFunctionFieldBar (N * q * ℓ))]
    (D : Divisor 𝕃 (modularFunctionFieldBar (N * q))) :
    Divisor.pushforwardAlong (heckeBetaBar 𝕃 N q) hβ₀
        (Divisor.pushforwardAlong (heckeAlphaBar 𝕃 (N * q) ℓ) hα₁
          (Divisor.pullbackAlong (heckeBetaBar 𝕃 (N * q) ℓ) hβ₁ D))
      = Divisor.pushforwardAlong (heckeAlphaBar 𝕃 N ℓ) hα₂
          (Divisor.pullbackAlong (heckeBetaBar 𝕃 N ℓ) hβ₂
            (Divisor.pushforwardAlong (heckeBetaBar 𝕃 N q) hβ₀ D)) := by
  have hM : N * q * ℓ = N * ℓ * q := Nat.mul_right_comm N q ℓ
  have hex : HeckeBetaExchangeAt 𝕃 N ℓ q (N * q * ℓ) hM :=
    heckeBetaExchangeAt_of_primes_of_ne 𝕃 N ℓ q (N * q * ℓ) Fact.out Fact.out hℓq hM
  have hu : (towerSubstBar 𝕃 (N * ℓ) q (dvd_of_eq_roof_beta N ℓ q _ hM).1).toRingHom.IsIntegral :=
    towerSubstBar_isIntegral 𝕃 q (dvd_of_eq_roof_beta N ℓ q _ hM).1
  have hu' : (towerSubstBar 𝕃 (N * q) ℓ (dvd_of_eq_roof_beta N ℓ q _ hM).2).toRingHom.IsIntegral :=
    towerSubstBar_isIntegral 𝕃 ℓ (dvd_of_eq_roof_beta N ℓ q _ hM).2
  rw [hex hβ₂ hβ₀ hu hu' D]
  have hc₁ : ((heckeAlphaBar 𝕃 (N * q) ℓ).comp (heckeBetaBar 𝕃 N q)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hβ₀ hα₁
  have hc₂ : ((towerSubstBar 𝕃 (N * ℓ) q (dvd_of_eq_roof_beta N ℓ q _ hM).1).comp
      (heckeAlphaBar 𝕃 N ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hα₂ hu
  rw [Divisor.pushforwardAlong_pushforwardAlong (heckeBetaBar 𝕃 N q)
        (heckeAlphaBar 𝕃 (N * q) ℓ) hβ₀ hα₁ hc₁,
      Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaBar 𝕃 N ℓ)
        (towerSubstBar 𝕃 (N * ℓ) q (dvd_of_eq_roof_beta N ℓ q _ hM).1) hα₂ hu hc₂]
  have h0 : N * q ∣ N * q * ℓ := dvd_mul_right (N * q) ℓ
  have e₁ : (heckeAlphaBar 𝕃 (N * q) ℓ).comp (heckeBetaBar 𝕃 N q) = towerSubstBar 𝕃 N q h0 := by
    rw [heckeAlphaBar_eq_towerInclBar]
    exact towerInclBar_comp_heckeBetaBar 𝕃 q h0
  have e₂ : (towerSubstBar 𝕃 (N * ℓ) q (dvd_of_eq_roof_beta N ℓ q _ hM).1).comp (heckeAlphaBar 𝕃 N ℓ)
      = towerSubstBar 𝕃 N q h0 :=
    towerSubstBar_comp_heckeAlphaBar 𝕃 q ℓ _ h0
  have hI : (towerSubstBar 𝕃 N q h0).toRingHom.IsIntegral := towerSubstBar_isIntegral 𝕃 q h0
  rw [Divisor.pushforwardAlong_congr'' e₁ hc₁ hI, Divisor.pushforwardAlong_congr'' e₂ hc₂ hI]
  congr 1

end Chains

end DegComm

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime)
    (ℓ : Nat.Primes) (hℓq : (ℓ : ℕ) ≠ q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∀ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
      (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
      (hαℓN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      (hβℓN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))]
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
        Finsupp.mapDomain (·.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
            (heckeDivBar hαℓ hβℓ D)
          = heckeDivBar hαℓN hβℓN
              (Finsupp.mapDomain
                (·.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) D) ∧
        Finsupp.mapDomain (·.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
            (heckeDivBar hαℓ hβℓ D)
          = heckeDivBar hαℓN hβℓN
              (Finsupp.mapDomain
                (·.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) D) := by
  intro hα hβ hαℓ hβℓ hαℓN hβℓN _ _ D
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  simp only [heckeDivBar, Divisor.correspondence_apply, ← DegComm.pushforwardAlong_eq_mapDomain]
  exact ⟨DegComm.alpha_chain N q ℓ hℓq hα hαℓ hβℓ hαℓN hβℓN D,
    DegComm.beta_chain N q ℓ hℓq hβ hαℓ hβℓ hαℓN hβℓN D⟩

end S_ModularCurve_mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne
end P2MW
export P2MW.S_ModularCurve_mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne (solution)
