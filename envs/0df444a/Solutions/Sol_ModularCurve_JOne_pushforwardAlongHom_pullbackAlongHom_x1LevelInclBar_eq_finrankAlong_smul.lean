-- Prove2me | solution 1 for ModularCurve.JOne.pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/1fdecf52-f96b-5ade-9460-f1a9add75187

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace TrioPushPull

theorem pushforwardAlongHom_pullbackAlongHom_eq_finrankAlong_smul
    {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin) (hsep : SeparableAlong K φ) (x : Pic0 K F) :
    Pic0.pushforwardAlongHom φ hφ hfin hN (Pic0.pullbackAlongHom φ hφ hFI x) = (finrankAlong K φ : ℤ) • x := by
  letI := algebraAlong φ
  letI : Module F F' := Algebra.toModule
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI hFI' : FundamentalIdentity K F F' := hFI
  haveI hMF : Module.Finite F F' := hfin
  haveI hSRI : SumRamificationInertia K F F' :=
    ⟨fun v => Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v⟩
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, Pic0.pushforwardAlongHom_mk]
  have hdiv : Divisor.pushforwardAlong φ hφ ((Pic0.pullbackAlongDegZeroHom φ hφ hFI D : Divisor K F')) =
      (Module.finrank F F' : ℤ) • (D : Divisor K F) := by
    rw [Pic0.coe_pullbackAlongDegZeroHom]
    exact Divisor.pushforward_pullback_of_finite (D : Divisor K F)
  have hsub : Pic0.pushforwardAlongDegZero φ hφ (Pic0.pullbackAlongDegZeroHom φ hφ hFI D) =
      (Module.finrank F F' : ℤ) • D := by
    apply Subtype.ext
    rw [Pic0.coe_pushforwardAlongDegZero]
    simpa using hdiv
  rw [hsub]
  show Pic0.mk _ = _
  rw [show (finrankAlong K φ : ℤ) = (Module.finrank F F' : ℤ) from rfl]
  exact map_zsmul (QuotientAddGroup.mk' _) _ D

end TrioPushPull

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
          (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI x) =
        ((AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) : ℕ) : ℤ) • x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro x
  haveI : CharZero ↥(ModularCurve.x1FunctionFieldBar N) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hsep : SeparableAlong (AlgebraicClosure ℚ) (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) := separableAlong_of_charZero _ hαint
  rw [TrioPushPull.pushforwardAlongHom_pullbackAlongHom_eq_finrankAlong_smul _ hαint hαFI hαfin hαN hsep x]

end S_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul
end P2MW
export P2MW.S_ModularCurve_JOne_pushforwardAlongHom_pullbackAlongHom_x1LevelInclBar_eq_finrankAlong_smul (solution)
