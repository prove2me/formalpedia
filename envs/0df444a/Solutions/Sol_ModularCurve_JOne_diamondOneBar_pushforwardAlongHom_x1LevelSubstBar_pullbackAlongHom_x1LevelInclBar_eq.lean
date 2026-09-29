-- Prove2me | solution 1 for ModularCurve.JOne.diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ba4eb725-041b-5cd0-af7e-8b9c0d433485

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_AlgebraicCurve_Divisor_pushforward_pullback_of_finite
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p
import Theorems.Thm_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

noncomputable section

open ModularCurve AlgebraicCurve

namespace JHTrio

open ModularCurve AlgebraicCurve

theorem coe_equivOfEq_apply {F E : Type*} [Field F] [Field E] [Algebra F E] {S T : IntermediateField F E}
    (h : S = T) (x : S) : ((IntermediateField.equivOfEq h x : T) : E) = (x : E) := rfl

theorem finrankAlong_algEquiv {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  rw [AlgEquiv.symm_comp, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

theorem finiteAlong_of_finrankAlong_pos {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : 0 < finrankAlong K φ) : FiniteAlong K φ := by
  letI alg : Algebra F F' := algebraAlong φ
  letI mdl : Module F F' := alg.toModule
  have h' : 0 < Module.finrank F F' := h
  have hfin : FiniteDimensional F F' := FiniteDimensional.of_finrank_pos h'
  exact hfin

theorem isIntegral_of_finiteAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (h : FiniteAlong K φ) : φ.toRingHom.IsIntegral := by
  letI alg : Algebra F F' := algebraAlong φ
  letI mdl : Module F F' := alg.toModule
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  intro x
  exact Algebra.IsIntegral.isIntegral (R := F) x

theorem pushforwardAlong_pullbackAlong_algEquiv {K R F : Type*} [Field K] [Field R] [Field F] [Algebra K R] [Algebra K F]
    [CharZero R] [HasPrincipalDivisors K F] (σ : R ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral) (D : Divisor K R) :
    Divisor.pushforwardAlong σ.toAlgHom hσ (Divisor.pullbackAlong σ.toAlgHom hσ D) = D := by
  have hfin : FiniteAlong K σ.toAlgHom := finiteAlong_of_finrankAlong_pos _ (by rw [finrankAlong_algEquiv]; exact Nat.one_pos)
  have hsep : SeparableAlong K σ.toAlgHom := separableAlong_of_charZero σ.toAlgHom hσ
  letI := algebraAlong σ.toAlgHom
  letI : Module R F := Algebra.toModule
  haveI := isScalarTower_along σ.toAlgHom
  haveI := isIntegral_along σ.toAlgHom hσ
  haveI hMF : Module.Finite R F := hfin
  haveI hSRI : SumRamificationInertia K R F :=
    ⟨fun v => Place.sum_ramificationIndexAlong_mul_inertiaDegAlong σ.toAlgHom hσ hfin hsep v⟩
  have h := Divisor.pushforward_pullback_of_finite (K := K) (F := R) (F' := F) D
  have h1 : Module.finrank R F = 1 := finrankAlong_algEquiv (K := K) σ
  rw [h1, Nat.cast_one, one_smul] at h
  exact h

theorem pushforwardAlong_comp_pullbackAlong_comp {K E R F : Type*} [Field K] [Field E] [Field R] [Field F]
    [Algebra K E] [Algebra K R] [Algebra K F] [CharZero R] [HasPrincipalDivisors K R] [HasPrincipalDivisors K F]
    (σ : R ≃ₐ[K] F) (hσ : σ.toAlgHom.toRingHom.IsIntegral)
    (a b : E →ₐ[K] R) (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (hσa : (σ.toAlgHom.comp a).toRingHom.IsIntegral) (hσb : (σ.toAlgHom.comp b).toRingHom.IsIntegral) (D : Divisor K E) :
    Divisor.pushforwardAlong (σ.toAlgHom.comp a) hσa (Divisor.pullbackAlong (σ.toAlgHom.comp b) hσb D) =
      Divisor.pushforwardAlong a ha (Divisor.pullbackAlong b hb D) := by
  rw [← Divisor.pullbackAlong_pullbackAlong b σ.toAlgHom hb hσ hσb D,
    ← Divisor.pushforwardAlong_pushforwardAlong a σ.toAlgHom ha hσ hσa,
    pushforwardAlong_pullbackAlong_algEquiv σ hσ]

theorem pullbackAlong_congr {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    [HasPrincipalDivisors K F] {φ ψ : E →ₐ[K] F} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (D : Divisor K E) : Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

theorem pushforwardAlong_congr {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    {φ ψ : E →ₐ[K] F} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (D : Divisor K F) : Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h; rfl

theorem pushforwardAlong_pullbackAlong_of_exchange {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    [CharZero F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (a b : E →ₐ[K] F) (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (τ : F ≃ₐ[K] F) (hτ : τ.toAlgHom.toRingHom.IsIntegral) (δ : E ≃ₐ[K] E) (hδ : δ.symm.toAlgHom.toRingHom.IsIntegral)
    (h₁ : τ.toAlgHom.comp a = b) (h₂ : τ.toAlgHom.comp b = a.comp δ.toAlgHom) (D : Divisor K E) :
    Divisor.pushforwardAlong b hb (Divisor.pullbackAlong a ha D) =
      Divisor.pushforwardAlong a ha (Divisor.pullbackAlong b hb (Divisor.pullbackAlong δ.symm.toAlgHom hδ D)) := by
  subst h₁
  have ha' : a = (τ.toAlgHom.comp (τ.toAlgHom.comp a)).comp δ.symm.toAlgHom := by
    rw [h₂]; ext x; simp
  have hττa : (τ.toAlgHom.comp (τ.toAlgHom.comp a)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ha hτ) hτ
  have hall : ((τ.toAlgHom.comp (τ.toAlgHom.comp a)).comp δ.symm.toAlgHom).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hδ hττa
  rw [pullbackAlong_congr ha' ha hall D,
    ← Divisor.pullbackAlong_pullbackAlong δ.symm.toAlgHom (τ.toAlgHom.comp (τ.toAlgHom.comp a)) hδ hττa hall,
    ← Divisor.pullbackAlong_pullbackAlong (τ.toAlgHom.comp a) τ.toAlgHom hb hτ hττa,
    ← Divisor.pushforwardAlong_pushforwardAlong a τ.toAlgHom ha hτ hb,
    pushforwardAlong_pullbackAlong_algEquiv τ hτ,
    ← Divisor.pullbackAlong_pullbackAlong a τ.toAlgHom ha hτ hb]

theorem pushforwardAlong_pullbackAlong_of_exchange' {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F]
    [CharZero F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (a b : E →ₐ[K] F) (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (τ : F ≃ₐ[K] F) (hτ : τ.toAlgHom.toRingHom.IsIntegral) (δ : E ≃ₐ[K] E) (hδ : δ.toAlgHom.toRingHom.IsIntegral)
    (h₁ : τ.toAlgHom.comp a = b) (h₂ : τ.toAlgHom.comp b = a.comp δ.toAlgHom) (D : Divisor K E) :
    Divisor.pushforwardAlong b hb (Divisor.pullbackAlong a ha D) =
      Divisor.pushforwardAlong δ.toAlgHom hδ (Divisor.pushforwardAlong a ha (Divisor.pullbackAlong b hb D)) := by
  subst h₁
  have hττa : (τ.toAlgHom.comp (τ.toAlgHom.comp a)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (RingHom.IsIntegral.trans _ _ ha hτ) hτ
  have haδ : (a.comp δ.toAlgHom).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hδ ha

  rw [← Divisor.pushforwardAlong_pushforwardAlong a τ.toAlgHom ha hτ hb]
  conv_lhs => rw [← pushforwardAlong_pullbackAlong_algEquiv τ hτ (Divisor.pullbackAlong a ha D)]
  rw [Divisor.pushforwardAlong_pushforwardAlong τ.toAlgHom τ.toAlgHom hτ hτ (RingHom.IsIntegral.trans _ _ hτ hτ),
    Divisor.pushforwardAlong_pushforwardAlong a (τ.toAlgHom.comp τ.toAlgHom) ha (RingHom.IsIntegral.trans _ _ hτ hτ) hττa,
    Divisor.pullbackAlong_pullbackAlong a τ.toAlgHom ha hτ hb,
    pushforwardAlong_congr (show (τ.toAlgHom.comp τ.toAlgHom).comp a = a.comp δ.toAlgHom by rw [AlgHom.comp_assoc, h₂]) hττa haδ,
    Divisor.pushforwardAlong_pushforwardAlong δ.toAlgHom a hδ ha haδ]

theorem pushforwardAlong_algEquiv_eq_pullbackAlong_symm {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero E]
    [HasPrincipalDivisors K E] (δ : E ≃ₐ[K] E) (hδ : δ.toAlgHom.toRingHom.IsIntegral) (hδ' : δ.symm.toAlgHom.toRingHom.IsIntegral)
    (Y : Divisor K E) :
    Divisor.pushforwardAlong δ.toAlgHom hδ Y = Divisor.pullbackAlong δ.symm.toAlgHom hδ' Y := by
  have hid : (δ.toAlgHom.comp δ.symm.toAlgHom).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hδ' hδ
  have hY : Divisor.pullbackAlong δ.toAlgHom hδ (Divisor.pullbackAlong δ.symm.toAlgHom hδ' Y) = Y := by
    rw [Divisor.pullbackAlong_pullbackAlong δ.symm.toAlgHom δ.toAlgHom hδ' hδ hid,
      pullbackAlong_congr (show δ.toAlgHom.comp δ.symm.toAlgHom = (AlgEquiv.refl : E ≃ₐ[K] E).toAlgHom by ext x; simp) hid
        (RingHom.isIntegral_of_surjective _ (AlgEquiv.refl : E ≃ₐ[K] E).surjective)]
    refine (Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul (AlgEquiv.refl : E ≃ₐ[K] E) _ Y).trans ?_
    show SemilinearAut.ofAlgAut (1 : E ≃ₐ[K] E) • Y = Y
    rw [map_one, one_smul]
  conv_lhs => rw [← hY]
  exact pushforwardAlong_pullbackAlong_algEquiv δ hδ _

theorem ofAlgAut_smul_pushforwardAlong_algEquiv {K E : Type*} [Field K] [Field E] [Algebra K E] [CharZero E]
    [HasPrincipalDivisors K E] (δ : E ≃ₐ[K] E) (hδ : δ.toAlgHom.toRingHom.IsIntegral) (Y : Divisor K E) :
    SemilinearAut.ofAlgAut δ • Divisor.pushforwardAlong δ.toAlgHom hδ Y = Y := by
  have hδ' : δ.symm.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ δ.symm.surjective
  have hid : (δ.toAlgHom.comp δ.symm.toAlgHom).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hδ' hδ
  rw [pushforwardAlong_algEquiv_eq_pullbackAlong_symm δ hδ hδ',
    show SemilinearAut.ofAlgAut δ • Divisor.pullbackAlong δ.symm.toAlgHom hδ' Y =
      Divisor.pullbackAlong (δ : E →ₐ[K] E) hδ (Divisor.pullbackAlong δ.symm.toAlgHom hδ' Y) from
      (Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul δ hδ _).symm,
    Divisor.pullbackAlong_pullbackAlong δ.symm.toAlgHom δ.toAlgHom hδ' hδ hid,
    pullbackAlong_congr (show δ.toAlgHom.comp δ.symm.toAlgHom = ((AlgEquiv.refl : E ≃ₐ[K] E) : E →ₐ[K] E) by ext x; simp) hid
      (RingHom.isIntegral_of_surjective _ (AlgEquiv.refl : E ≃ₐ[K] E).surjective),
    Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul]
  show SemilinearAut.ofAlgAut (1 : E ≃ₐ[K] E) • Y = Y
  rw [map_one, one_smul]

theorem ofAlgAut_smul_pushforwardAlongHom_pullbackAlongHom_of_exchange
    {K E F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [CharZero E] [CharZero F]
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (a b : E →ₐ[K] F) (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (haFI : FundamentalIdentityAlong K a ha) (hbFI : FundamentalIdentityAlong K b hb)
    (hafin : FiniteAlong K a) (hbfin : FiniteAlong K b) (haN : NormFormulaAlong K a hafin) (hbN : NormFormulaAlong K b hbfin)
    (τ : F ≃ₐ[K] F) (δ : E ≃ₐ[K] E)
    (h₁ : τ.toAlgHom.comp a = b) (h₂ : τ.toAlgHom.comp b = a.comp δ.toAlgHom) (x : Pic0 K E) :
    SemilinearAut.ofAlgAut δ • Pic0.pushforwardAlongHom b hb hbfin hbN (Pic0.pullbackAlongHom a ha haFI x) =
      Pic0.pushforwardAlongHom a ha hafin haN (Pic0.pullbackAlongHom b hb hbFI x) := by
  have hτ : τ.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ τ.surjective
  have hδ : δ.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ δ.surjective
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.pullbackAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.pushforwardAlongHom_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pullbackAlongDegZeroHom,
    Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pullbackAlongDegZeroHom,
    pushforwardAlong_pullbackAlong_of_exchange' a b ha hb τ hτ δ hδ h₁ h₂, ofAlgAut_smul_pushforwardAlong_algEquiv]

end JHTrio

end

namespace X1PD
theorem xHFunctionFieldBar_bot (M : ℕ) :
    ModularCurve.xHFunctionFieldBar M ⊥ = ModularCurve.x1FunctionFieldBar M := by
  show ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldC ℚ M ⊥) =
    ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldC ℚ M)
  rw [ModularCurve.xHFunctionFieldC_bot]

theorem hasPrincipalDivisors_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by
  have h := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M ⊥
  rwa [xHFunctionFieldBar_bot] at h
end X1PD

open ModularCurve AlgebraicCurve in
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
      ModularCurve.diamondOneBar N p
          (AlgebraicCurve.Pic0.pushforwardAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβfin hβN
            (AlgebraicCurve.Pic0.pullbackAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαFI x)) =
        AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) hαint hαfin hαN
          (AlgebraicCurve.Pic0.pullbackAlongHom (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularCurve.x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p))) hβint hβFI x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro x

  have hcopZ : IsCoprime (p : ℤ) (N : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpN
  obtain ⟨w₀, y', hwy⟩ := hcopZ

  set y : ℤ := -y' with hy
  have hrel : (p : ℤ) * w₀ - (N : ℤ) * y = 1 := by rw [hy]; linarith [hwy]

  let γ : SL(2, ℤ) := ⟨!![1, y; (N : ℤ), (p : ℤ) * w₀], by rw [Matrix.det_fin_two_of]; linarith [hrel]⟩
  let γ' : SL(2, ℤ) := ⟨!![w₀, -y; -(N : ℤ), (p : ℤ)], by rw [Matrix.det_fin_two_of]; linarith [hrel]⟩

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ιC : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom

  obtain ⟨τ, -, hE1, -, -⟩ := ModularCurve.XOneP.exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p p N hpN y w₀ hrel
    γ γ' rfl rfl ιC

  have hIn := ModularCurve.heckeDiamondInputsAll N
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpN
  have hdia : IsDiamondAut N p (diamondAut N p) := by
    have h := (hIn.2 p hcop).1
    rw [diamondAut, dif_pos h]; exact h.choose_spec
  have hbc : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut N p) (diamondAutBar N p) := by
    have h := (hIn.2 p hcop).2
    rw [diamondAutBar, baseChangeAut, dif_pos h]; exact h.choose_spec

  have h0 : HeckeBetaOneDefined N p := (hIn.1 ⟨p, Fact.out⟩).fst
  obtain ⟨h₁, h₂⟩ := ModularCurve.XOneP.comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p p N hpN y w₀ hrel γ γ' rfl rfl ιC τ hE1
    (x1LevelInclBar (AlgebraicClosure ℚ) (dvd_mul_right N p)) (x1LevelSubstBar (AlgebraicClosure ℚ) p (dvd_refl (N * p)))
    (fun u => coe_x1LevelInclBar (AlgebraicClosure ℚ) _ u) (fun u => coe_x1LevelSubstBar_of (AlgebraicClosure ℚ) p _ h0 u) hdia hbc
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar N) := X1PD.hasPrincipalDivisors_x1FunctionFieldBar N
  haveI : CharZero ↥(x1FunctionFieldBar N) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : CharZero ↥(x1FunctionFieldBar (N * p)) := charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  rw [diamondOneBar_apply]
  exact JHTrio.ofAlgAut_smul_pushforwardAlongHom_pullbackAlongHom_of_exchange _ _ hαint hβint hαFI hβFI hαfin hβfin hαN hβN τ
    (diamondAutBar N p) h₁ h₂ x

end S_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq
end P2MW
export P2MW.S_ModularCurve_JOne_diamondOneBar_pushforwardAlongHom_x1LevelSubstBar_pullbackAlongHom_x1LevelInclBar_eq (solution)
