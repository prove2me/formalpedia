-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mem_chartAlgInf_coeff_zero_eq_zero_forall_algEquiv_coeff_zero_ne_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d6727c63-5e9e-5952-a0c2-958998a0a5f8

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_FullLevel_exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH
import Theorems.Thm_ModularCurve_FullLevel_exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mem_chartAlgInf_coeff_zero_eq_zero_forall_algEquiv_coeff_zero_ne_xH
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace CWAsm

open ModularCurve

theorem intSeriesC_ne_zero (K : Type) [Field K] [CharZero K] {p : PowerSeries ℤ} (hp : p ≠ 0) :
    intSeriesC K p ≠ 0 := by
  intro h
  apply hp
  ext n
  have h1 := congrArg (fun x : LaurentSeries K => x.coeff (n : ℤ)) h
  simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, HahnSeries.coeff_zero,
    Int.coe_castRingHom, Int.cast_eq_zero] at h1
  simpa using h1

theorem intSeriesC_coeff_natCast (K : Type) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    (intSeriesC K p).coeff (n : ℤ) = ((PowerSeries.coeff n p : ℤ) : K) := by
  simp [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

theorem intSeriesC_coeff_of_neg (K : Type) [Field K] (p : PowerSeries ℤ) {n : ℤ} (hn : n < 0) :
    (intSeriesC K p).coeff n = 0 := by
  rw [intSeriesC]
  exact ModularCurve.ofPowerSeries_coeff_of_neg _ hn

theorem coeffEmb_intSeriesC (L : Type) [Field L] [CharZero L] (p : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  ext n
  rw [coeffEmb_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [intSeriesC_coeff_of_neg ℚ p hn, intSeriesC_coeff_of_neg L p hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [intSeriesC_coeff_natCast, intSeriesC_coeff_natCast, map_intCast]

end CWAsm

open CWAsm ModularCurve AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j ∧
      ((b : ↥K) : LaurentSeries L).coeff 0 = 0 ∧
      ∀ σ : ↥K ≃ₐ[L] ↥K,
        (∀ x : ↥K, (x : LaurentSeries L) ∈
          ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → σ x = x) →
        σ ≠ AlgEquiv.refl →
        ∀ c ∈ IsLocalRing.maximalIdeal A, ((σ b : ↥K) : LaurentSeries L).coeff 0 ≠ algebraMap A L c := by
  classical
  set N : ℕ := q ^ 2 * M' with hN

  obtain ⟨k, f, g, pf, pg, h, hf, hg, hpg0, hfgh, hh0, hint, hslash⟩ :=
    ModularCurve.FullLevel.exists_integralForms_levelH_coeff_zero_eq_zero_isIntegralElem_slash_isUnit q M'
  obtain ⟨ρ, hρa, hρb, hρc, hρd⟩ :=
    ModularCurve.FullLevel.exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH q hq M' hqM' L K hK

  have hpgL : intSeriesC L pg ≠ 0 := intSeriesC_ne_zero L hpg0
  have hpgQ : intSeriesC ℚ pg ≠ 0 := intSeriesC_ne_zero ℚ hpg0
  have hratio : intSeriesC ℚ pf / intSeriesC ℚ pg = intSeriesC ℚ h := by
    rw [hfgh, intSeriesC_mul, mul_div_cancel_left₀ _ hpgQ]
  have hmemQ : intSeriesC ℚ h ∈ ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') := by
    rw [← hratio]
    exact div_mem_qExpFunctionFieldC f g hf hg hpgQ
  have hmem : intSeriesC L h ∈ K := by
    rw [hK, ← coeffEmb_intSeriesC]
    exact coeffEmb_mem_laurentBaseChange L hmemQ
  set b : ↥K := ⟨intSeriesC L h, hmem⟩ with hbdef
  have hbcoe : ((b : ↥K) : LaurentSeries L) = intSeriesC L h := rfl
  have hbratio : ((b : ↥K) : LaurentSeries L) = intSeriesC L pf / intSeriesC L pg := by
    rw [hbcoe, hfgh, intSeriesC_mul, mul_div_cancel_left₀ _ hpgL]
  refine ⟨b, ?_, ?_, ?_⟩
  ·
    obtain ⟨p, hpm, hp0⟩ := hint
    rw [mem_chartAlg_iff]
    have hjmem : (j : ↥K)⁻¹ ∈ Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K) := Algebra.subset_adjoin (Set.mem_singleton _)
    let ψ : Polynomial ℤ →+* ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) :=
      (Polynomial.aeval (R := ℤ) (⟨(j : ↥K)⁻¹, hjmem⟩ : ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)))).toRingHom
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩

    let θ : Polynomial ℤ →+* ↥K := (Polynomial.aeval (R := ℤ) ((j : ↥K)⁻¹)).toRingHom
    have hθ : (algebraMap ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) ↥K).comp ψ = θ := by
      refine Polynomial.ringHom_ext (fun n => by simp [ψ, θ]) ?_
      simp [ψ, θ, Polynomial.aeval_X]
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_map, hθ, ← Polynomial.eval₂_eq_eval_map]

    let ι : ↥K →+* LaurentSeries L := (IntermediateField.val K).toRingHom
    have hι : Function.Injective ι := fun x y hxy => Subtype.ext hxy
    apply hι
    rw [map_zero, Polynomial.hom_eval₂]
    have hcomp : ι.comp θ = (ModularCurve.coeffEmb L).comp (Polynomial.eval₂RingHom (algebraMap ℤ (LaurentSeries ℚ)) (ModularCurve.jq)⁻¹) := by
      refine Polynomial.ringHom_ext (fun n => by simp [ι, θ]) ?_
      simp only [RingHom.coe_comp, Function.comp_apply, θ, ι, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, map_inv₀, hj.symm]
      rfl
    have hιb : ι b = ModularCurve.coeffEmb L (intSeriesC ℚ h) := by rw [coeffEmb_intSeriesC]; rfl
    rw [hcomp, hιb, ← Polynomial.hom_eval₂, hp0, map_zero]
  ·
    rw [hbcoe, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, intSeriesC_coeff_natCast, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hh0, Int.cast_zero]
  ·
    intro σ hσ hσ1 c hc
    obtain ⟨γ, rfl⟩ := hρc σ hσ
    have hγ : CohCarrier.gamma0Units (q ^ 2 * M') γ ∉
        ModularCurve.FullLevel.levelH q M' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M'))ˣ) := by
      intro hmem'
      exact hσ1 ((hρd γ).mpr hmem')
    obtain ⟨f₁, g₁, pf₁, pg₁, h₁, c₁, hc₁, hf₁, hg₁, hf₁s, hg₁s, hpg₁0, hfgh₁, hunit⟩ := hslash γ
    have hpg₁L : intSeriesC L pg₁ ≠ 0 := intSeriesC_ne_zero L hpg₁0
    have hσb : ((ρ γ b : ↥K) : LaurentSeries L) = intSeriesC L h₁ := by
      rw [hρa γ f g f₁ g₁ c₁ hc₁ hf hg hf₁ hg₁ hf₁s hg₁s hpgL hpg₁L b hbratio, hfgh₁, intSeriesC_mul,
        mul_div_cancel_left₀ _ hpg₁L]
    obtain ⟨u, hu⟩ := hunit hγ
    intro he
    rw [hσb, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, intSeriesC_coeff_natCast,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hu] at he

    have hcu : c = ((u : ℤ) : A) := by
      apply IsFractionRing.injective A L
      rw [← he, ← map_intCast (algebraMap A L)]
    have : IsUnit c := by rw [hcu]; exact (Units.map (Int.castRingHom A).toMonoidHom u).isUnit
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.eq_top_of_isUnit_mem _ hc this)

end S_ModularCurve_FullLevel_exists_mem_chartAlgInf_coeff_zero_eq_zero_forall_algEquiv_coeff_zero_ne_xH
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mem_chartAlgInf_coeff_zero_eq_zero_forall_algEquiv_coeff_zero_ne_xH (solution)
