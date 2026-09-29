-- Prove2me | solution 1 for ModularCurve.XOneP.exists_fin_span_heckeRoof_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c0c36506-6889-5714-88c7-516e04d8eb3a

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Theorems.Thm_ModularCurve_qExpand_mem_x1x0FunctionFieldC_mul_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_fin_span_heckeRoof_x1_mul
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open scoped BigOperators

namespace LegDegSpanPen14

theorem dvd_mul_iff {ℓ p M : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p) : ℓ ∣ M * p ↔ ℓ ∣ M := by
  constructor
  · intro h
    rcases hℓ.dvd_mul.mp h with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h) hℓp
  · intro h
    exact dvd_mul_of_dvd_left h p

theorem exists_span_of_finrankAlong {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']
    (φ : F →ₐ[L] F') {d : ℕ} (hd : AlgebraicCurve.finrankAlong L φ = d) (hpos : 0 < d) :
    ∃ b : Fin d → F', ∀ z : F', ∃ c : Fin d → F, z = ∑ i, φ (c i) * b i := by
  letI : Algebra F F' := AlgebraicCurve.algebraAlong φ
  have hfr : Module.finrank F F' = d := hd
  haveI : Module.Finite F F' := Module.finite_of_finrank_pos (hfr ▸ hpos)
  let B := Module.finBasisOfFinrankEq F F' hfr
  refine ⟨fun i => B i, fun z => ⟨fun i => B.repr z i, ?_⟩⟩
  conv_lhs => rw [← B.sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def]
  rfl

end LegDegSpanPen14

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (ι : ↥K →ₐ[L] ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hι : (∀ f : ↥K, ((ι f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = (f : LaurentSeries L)) ∨
      (∀ f : ↥K, ((ι f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ModularCurve.qExpand L ℓ (f : LaurentSeries L))) :
    ∃ b : Fin (if ℓ ∣ M then ℓ else ℓ + 1) → ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))),
      ∀ z : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))), ∃ c : Fin (if ℓ ∣ M then ℓ else ℓ + 1) → ↥K, z = ∑ i, ι (c i) * b i := by
  classical
  subst hK
  have hℓ : ℓ.Prime := Fact.out
  have hp : p.Prime := Fact.out
  set d : ℕ := if ℓ ∣ M then ℓ else ℓ + 1 with hd_def
  have hdpos : 0 < d := by
    rw [hd_def]; split_ifs <;> have := hℓ.pos <;> omega
  have hdMp : (if ℓ ∣ M * p then ℓ else ℓ + 1) = d := by
    rw [hd_def]
    exact if_congr (LegDegSpanPen14.dvd_mul_iff hℓ hp hℓp) rfl rfl

  have hι' : AlgebraicCurve.finrankAlong L ι = d := by
    rcases hι with h | h
    · have heq : ι = ModularCurve.heckeAlphaOneBar L (M * p) ℓ :=
        AlgHom.ext fun f => Subtype.ext ((h f).trans (ModularCurve.coe_heckeAlphaOneBar (M * p) ℓ f).symm)
      rw [heq, ModularCurve.finrankAlong_heckeAlphaOneBar L (M * p) ℓ, hdMp]
    · have hdef : ModularCurve.HeckeBetaOneDefined (M * p) ℓ := by
        intro y hy
        have hy' : y ∈ ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * 1) :=
          ModularCurve.x1FunctionFieldC_le_x1x0 ℚ (M * p) (M * p * 1) hy
        simpa only [mul_one] using ModularCurve.qExpand_mem_x1x0FunctionFieldC_mul_of_mem (M * p) 1 ℓ hy'
      have heq : ι = ModularCurve.heckeBetaOneBar L (M * p) ℓ :=
        AlgHom.ext fun f => Subtype.ext ((h f).trans (ModularCurve.coe_heckeBetaOneBar (M * p) ℓ hdef f).symm)
      rw [heq, ModularCurve.finrankAlong_heckeBetaOneBar L (M * p) ℓ hdef, hdMp]
  exact LegDegSpanPen14.exists_span_of_finrankAlong ι hι' hdpos

end S_ModularCurve_XOneP_exists_fin_span_heckeRoof_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_fin_span_heckeRoof_x1_mul (solution)
