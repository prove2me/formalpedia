-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/349390a0-cb0a-5491-8a01-e7646fac7281

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "CategoryTheory AlgebraicCurve ModularCurve~coeffMap_injective ModularCurve.XHDRLevel IsLocalRing"
open scoped MatrixGroups TensorProduct

namespace XHRD

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)

theorem ringHom_ext_zp {P : Type*} [Semiring P] (f g : ℤp →+* P) : f = g := by
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)]
    exact Nat.prime_iff_prime_int.mp Fact.out
  haveI : IsLocalization.AtPrime ℤp (Ideal.span {(p : ℤ)}) := GaloisRep.isLocalization_ratLocalizedAt Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (RingHom.ext_int _ _)

theorem coeffEmb_coeffMap_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (R : Type*) [CommRing R] [Algebra R ℚ]
    [Algebra R L] [IsScalarTower R ℚ L] (y : LaurentSeries R) :
    coeffMap (algebraMap R L) y = coeffEmb L (coeffMap (algebraMap R ℚ) y) := by
  ext n
  show algebraMap R L (y.coeff n) = algebraMap ℚ L (algebraMap R ℚ (y.coeff n))
  rw [← IsScalarTower.algebraMap_apply]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  exact this

end XHRD

open XHRD in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (htheta : ∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      (((theta (iota0 b) : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) :
    ∃ θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p)),
      (∀ c, θ 1 c = θ 0 (theta c)) ∧
      (∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
        coeffMap (algebraMap (R p) ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        θ 0 c = coeffMap (GaloisRep.ratLocalizedAtResidue p) y) ∧
      RingHom.ker (θ 0) ≠ RingHom.ker (θ 1) ∧
      (Ideal.span {((p : ℕ) : ↥(chartAlgFin p (ΓM M H) hj))}).minimalPrimes = {RingHom.ker (θ 0), RingHom.ker (θ 1)} ∧
      (∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = θ 0 (iota0 b) ^ p) ∧
      (∀ b : ↥(chartAlgFin p (ΓN p M H hpM) hj), θ 0 (theta (iota0 b)) = qExpand (ZMod p) p (θ 0 (iota0 b))) := by
  classical

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime p A hA
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime p A hA
  obtain ⟨θA, h1, h2, h3, h4, h5, h5', -, -⟩ :=
    ModularCurve.XHDRLevel.exists_ringHom_laurentSeries_pair_chartAlgFin_gammaH
      p M H hpM hpM2 hHp hj iota0 iota0_spec theta htheta A hA ρ hρ

  let ι : ZMod p →+* ResidueField ↥A := ZMod.castHom (dvd_refl p) (ResidueField ↥A)
  have hι : Function.Injective ι := ι.injective
  have hres : (residue ↥A).comp ρ = ι.comp (GaloisRep.ratLocalizedAtResidue p) := ringHom_ext_zp _ _
  let cι : LaurentSeries (ZMod p) →+* LaurentSeries (ResidueField ↥A) := coeffMap ι
  have hcι : Function.Injective cι := coeffMap_injective ι hι

  obtain ⟨hlift, -⟩ := ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj)
  have hread : ∀ (c : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      θA 0 c = cι (coeffMap (GaloisRep.ratLocalizedAtResidue p) y) := by
    intro c y hy
    have hyA : coeffMap A.subtype (coeffMap ρ y) =
        coeffEmb (AlgebraicClosure ℚ) (((c : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := by
      rw [ModularCurve.coeffMap_coeffMap, hρ, ← hy, coeffEmb_coeffMap_algebraMap]
    rw [h2 c _ hyA, ModularCurve.coeffMap_coeffMap, hres, ← ModularCurve.coeffMap_coeffMap]
  have hrange : ∀ c : ↥(chartAlgFin p (ΓM M H) hj), θA 0 c ∈ cι.range := by
    intro c
    obtain ⟨y, hy⟩ := hlift c
    exact ⟨_, (hread c y hy).symm⟩

  let e : LaurentSeries (ZMod p) ≃+* ↥cι.range :=
    RingEquiv.ofBijective cι.rangeRestrict
      ⟨fun a b h => hcι (congrArg Subtype.val h), RingHom.rangeRestrict_surjective cι⟩
  have he : ∀ w : ↥cι.range, cι (e.symm w) = (w : LaurentSeries (ResidueField ↥A)) := fun w => by
    have := congrArg Subtype.val (e.apply_symm_apply w)
    exact this
  let θ0 : ↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p) := e.symm.toRingHom.comp ((θA 0).codRestrict cι.range hrange)
  have hθ0 : ∀ c, cι (θ0 c) = θA 0 c := fun c => he ⟨θA 0 c, hrange c⟩
  let θ : Fin 2 → (↥(chartAlgFin p (ΓM M H) hj) →+* LaurentSeries (ZMod p)) := ![θ0, θ0.comp theta.toRingEquiv.toRingHom]
  have hθ_zero : ∀ c, θ 0 c = θ0 c := fun c => rfl
  have hθ_one : ∀ c, θ 1 c = θ0 (theta c) := fun c => rfl
  have hθ1 : ∀ c, cι (θ 1 c) = θA 1 c := fun c => by rw [hθ_one, hθ0, h1]
  have hker : ∀ i, RingHom.ker (θ i) = RingHom.ker (θA i) := by
    intro i
    ext c
    rw [RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff cι hcι]
    fin_cases i
    · change cι (θ 0 c) = 0 ↔ θA 0 c = 0
      rw [hθ_zero, hθ0]
    · change cι (θ 1 c) = 0 ↔ θA 1 c = 0
      rw [hθ1]

  refine ⟨θ, fun c => hθ_one c, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro c y hy
    apply hcι
    rw [hθ_zero, hθ0, hread c y hy]
  · rw [hker 0, hker 1]; exact h3
  · rw [hker 0, hker 1]; exact h4
  · intro b
    apply hcι
    rw [hθ_zero, hθ0, map_pow, hθ_zero (iota0 b), hθ0, h5]
  · intro b
    apply hcι
    rw [hθ_zero, hθ0, h5', hθ_zero (iota0 b)]
    change _ = coeffMap ι (qExpand (ZMod p) p (θ0 (iota0 b)))
    rw [coeffMap_qExpand]
    change _ = qExpand _ p (cι (θ0 (iota0 b)))
    rw [hθ0]

end

end S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_ringHom_laurentSeries_zmod_pair_chartAlgFin_gammaH (solution)
