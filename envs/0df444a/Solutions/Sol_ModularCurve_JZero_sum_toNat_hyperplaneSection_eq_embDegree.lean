-- Prove2me | solution 1 for ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7732791d-1026-5595-82bf-ab52bdfd64f4

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

private theorem sum_toNat_engine (N : ℕ) [NeZero N] (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    (B.sum fun _ n => n.toNat) = k * embDegree N := by
  classical
  obtain ⟨Du, hDu, hDu0⟩ :=
    (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor u hu
  have hB0 : ∀ w, 0 ≤ B w := by
    intro w
    rcases mem_riemannRochSpace_iff.mp huL w with h0 | h
    · exact absurd h0 hu
    · rw [hB w]
      linarith
  have hBeq : B = Du + (k : ℤ) • embDivisor N := by
    ext w
    rw [Finsupp.add_apply, hB w, hDu w]
  have hdegE : Divisor.degree (embDivisor N) = (embDegree N : ℤ) := by
    rw [ModularCurve.embDivisor, map_zsmul, Divisor.degree_single, one_mul,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one,
      smul_eq_mul, mul_one]
  have hdegB : Divisor.degree B = (k : ℤ) * embDegree N := by
    rw [hBeq, map_add, hDu0, zero_add, map_zsmul, hdegE, smul_eq_mul]
  have hz : ((B.sum fun _ n => n.toNat : ℕ) : ℤ) = (k : ℤ) * (embDegree N : ℤ) := by
    rw [Finsupp.sum, Nat.cast_sum]
    have hterm : ∀ w ∈ B.support, ((B w).toNat : ℤ) = B w * ((w.deg : ℕ) : ℤ) := by
      intro w _
      rw [Int.toNat_of_nonneg (hB0 w), ModularCurve.deg_eq_one_modularFunctionFieldBar N w,
        Nat.cast_one, mul_one]
    rw [Finset.sum_congr rfl hterm, ← AlgebraicCurve.Divisor.degree_eq_sum, hdegB]
  exact_mod_cast hz

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0)
    (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) :
    (Za.sum fun _ n => n.toNat) = embDegree N := by
  have hmem0 : linSec s a ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmem : linSec s a ∈ riemannRochSpace (((1 : ℕ) : ℤ) • embDivisor N) := by
    rw [Nat.cast_one, one_smul]
    exact hs.2 ▸ hmem0
  have h := sum_toNat_engine N 1 (linSec s a) ha hmem Za fun w => by
    rw [hZa w, Nat.cast_one, one_smul]
  simpa using h

end S_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
end P2MW
export P2MW.S_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree (solution)
