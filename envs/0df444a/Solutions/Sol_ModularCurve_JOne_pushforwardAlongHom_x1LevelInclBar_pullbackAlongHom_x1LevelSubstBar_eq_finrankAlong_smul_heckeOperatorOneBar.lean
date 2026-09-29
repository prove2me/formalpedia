-- Prove2me | solution 1 for ModularCurve.JOne.pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4871c3d7-ee2b-58a0-90ed-89f452966b70

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_AlgebraicCurve_Divisor_pushforward_pullback_of_finite
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_finiteAlong_x1x0LevelInclBar
import Theorems.Thm_ModularCurve_isIntegral_x1x0LevelInclBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace X1Trio

theorem pullbackAlong_congr {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    [HasPrincipalDivisors K F] {φ ψ : E →ₐ[K] F} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (D : Divisor K E) : Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

theorem pushforwardAlong_congr {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    {φ ψ : E →ₐ[K] F} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (D : Divisor K F) : Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h; rfl

theorem pushforwardAlong_pullbackAlong_eq_finrankAlong_smul {K R F : Type*} [Field K] [Field R] [Field F] [Algebra K R] [Algebra K F]
    [HasPrincipalDivisors K F] (j : R →ₐ[K] F) (hj : j.toRingHom.IsIntegral) (hfin : FiniteAlong K j) (hsep : SeparableAlong K j)
    (D : Divisor K R) :
    Divisor.pushforwardAlong j hj (Divisor.pullbackAlong j hj D) = (finrankAlong K j : ℤ) • D := by
  letI := algebraAlong j
  letI : Module R F := Algebra.toModule
  haveI := isScalarTower_along j
  haveI := isIntegral_along j hj
  haveI hMF : Module.Finite R F := hfin
  haveI hSRI : SumRamificationInertia K R F := ⟨fun v => Place.sum_ramificationIndexAlong_mul_inertiaDegAlong j hj hfin hsep v⟩
  exact Divisor.pushforward_pullback_of_finite (K := K) (F := R) (F' := F) D

end X1Trio

set_option maxHeartbeats 1600000 in

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (N * p))]
    (hαint : (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)).toRingHom.IsIntegral)
    (hβint : (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).toRingHom.IsIntegral)
    (hαFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint)
    (hβFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint)
    (hαfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)))
    (hβfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))))
    (hαN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαfin)
    (hβN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβfin) :
    ∀ x : ModularCurve.JOne N,
      AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαfin hαN
          (AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI x) =
        ((AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) •
          ModularCurve.heckeOperatorOneBar N ⟨p, Fact.out⟩ x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro x

  obtain ⟨h0, hα', hβ', hP', hfin', hFI', hN'⟩ := (ModularCurve.heckeDiamondInputsAll N).1 ⟨p, Fact.out⟩
  haveI := hP'
  rw [heckeOperatorOneBar_apply, heckeOperatorOneAlong_eq h0 hα' hβ' hFI' hfin' hN']

  have hj : (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).toRingHom.IsIntegral :=
    ModularCurve.isIntegral_x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))
  have hjfin : FiniteAlong (AlgebraicClosure ℚ) (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) :=
    ModularCurve.finiteAlong_x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))
  haveI : CharZero ↥(laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ N (N * p))) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hjsep : SeparableAlong (AlgebraicClosure ℚ) (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) :=
    separableAlong_of_charZero _ hj

  have eα : x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p) =
      (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).comp (heckeAlphaOneBar (AlgebraicClosure ℚ) N p) := by
    apply AlgHom.ext; intro u; apply Subtype.ext
    rw [coe_x1LevelInclBar, AlgHom.comp_apply, coe_x1x0LevelInclBar, coe_heckeAlphaOneBar]
  have hjα : ((x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).comp (heckeAlphaOneBar (AlgebraicClosure ℚ) N p)).toRingHom.IsIntegral :=
    eα ▸ hαint

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  show _ = ((finrankAlong (AlgebraicClosure ℚ) (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) •
    Pic0.correspondence _ _ _ _ _ _ _ (Pic0.mk D)
  rw [Pic0.correspondence_mk]
  have hdiv : Divisor.pushforwardAlong (x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint
      (Divisor.pullbackAlong (x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N))) =
      ((finrankAlong (AlgebraicClosure ℚ) (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) •
        Divisor.correspondence (heckeBetaOneBar (AlgebraicClosure ℚ) N p) (heckeAlphaOneBar (AlgebraicClosure ℚ) N p) hβ' hα'
          (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)) := by
    rw [Divisor.correspondence_apply, X1Trio.pushforwardAlong_congr eα hαint hjα,
      ← Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaOneBar (AlgebraicClosure ℚ) N p) _ hα' hj hjα]
    show Divisor.pushforwardAlong (heckeAlphaOneBar (AlgebraicClosure ℚ) N p) hα'
        (Divisor.pushforwardAlong _ hj (Divisor.pullbackAlong ((x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))).comp
          (heckeBetaOneBar (AlgebraicClosure ℚ) N p)) hβint (D : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)))) = _
    rw [← Divisor.pullbackAlong_pullbackAlong (heckeBetaOneBar (AlgebraicClosure ℚ) N p) _ hβ' hj hβint,
      X1Trio.pushforwardAlong_pullbackAlong_eq_finrankAlong_smul _ hj hjfin hjsep, map_zsmul]
  have hsub : Pic0.pushforwardAlongDegZero (x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint
      (Pic0.pullbackAlongDegZeroHom (x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI D) =
      ((finrankAlong (AlgebraicClosure ℚ) (x1x0LevelInclBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) : ℕ) : ℤ) •
        Pic0.degZeroCorrespondence (heckeBetaOneBar (AlgebraicClosure ℚ) N p) (heckeAlphaOneBar (AlgebraicClosure ℚ) N p) hβ' hα' hFI' D := by
    apply Subtype.ext
    rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pullbackAlongDegZeroHom]
    simpa [Pic0.coe_degZeroCorrespondence] using hdiv
  rw [hsub]
  exact map_zsmul (QuotientAddGroup.mk' _) _ _

end S_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar
end P2MW
export P2MW.S_ModularCurve_JOne_pushforwardAlongHom_x1LevelInclBar_pullbackAlongHom_x1LevelSubstBar_eq_finrankAlong_smul_heckeOperatorOneBar (solution)
