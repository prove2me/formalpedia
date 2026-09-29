-- Prove2me | solution 1 for ModularCurve.nonempty_lambdaModularPolynomialData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e99c5a23-cd53-5d69-84ee-32c63a5eeaed

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
import Theorems.Thm_ModularCurve_minpoly_lambdaNModC_coeff_mem_adjoin
import Theorems.Thm_ModularCurve_intCoeffs_minpoly_lambdaNModC_coeff
import Theorems.Thm_ModularCurve_aeval_lambdaModC_intCoeffs_descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_lambdaModularPolynomialData
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open Polynomial ModularCurve ModularCurve.PhiGen

noncomputable section

namespace LambdaPacketSol

local notation "L" => LaurentSeries ℚ

abbrev Fμ : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set L)

variable (q : ℕ) [hq : Fact q.Prime]

abbrev m : Polynomial Fμ := minpoly Fμ (lambdaNModC ℚ q)

theorem aeval_mu_injective : Function.Injective (aeval (R := ℚ) (lambdaModC ℚ) : Polynomial ℚ →ₐ[ℚ] L) :=
  transcendental_iff_injective.mp (ModularCurve.transcendental_lambdaModC ℚ)

theorem finrank_eq (hq2 : q ≠ 2) : Module.finrank Fμ (↥(IntermediateField.adjoin Fμ ({lambdaNModC ℚ q} : Set L))) = q + 1 :=
  ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC ℚ q hq2

theorem isIntegral_muq (hq2 : q ≠ 2) : IsIntegral Fμ (lambdaNModC ℚ q) := by
  have hpos : 0 < Module.finrank Fμ (↥(IntermediateField.adjoin Fμ ({lambdaNModC ℚ q} : Set L))) := by
    rw [finrank_eq q hq2]; omega
  haveI : Module.Finite Fμ (↥(IntermediateField.adjoin Fμ ({lambdaNModC ℚ q} : Set L))) :=
    Module.finite_of_finrank_pos hpos
  have h1 : IsIntegral Fμ (⟨lambdaNModC ℚ q, IntermediateField.mem_adjoin_simple_self Fμ (lambdaNModC ℚ q)⟩ :
      ↥(IntermediateField.adjoin Fμ ({lambdaNModC ℚ q} : Set L))) := IsIntegral.of_finite Fμ _
  exact h1.algebraMap

theorem natDegree_m (hq2 : q ≠ 2) : (m q).natDegree = q + 1 := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_muq q hq2), finrank_eq q hq2]

theorem monic_m (hq2 : q ≠ 2) : (m q).Monic := minpoly.monic (isIntegral_muq q hq2)

theorem exists_intPoly (hq2 : q ≠ 2) (k : ℕ) :
    ∃ P : Polynomial ℤ, aeval (lambdaModC ℚ) (P.map (Int.castRingHom ℚ)) = ((m q).coeff k : L) := by
  have hmem := ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin q hq2 k
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem
  obtain ⟨P, hP⟩ := hmem
  have hint : IntCoeffs (aeval (lambdaModC ℚ) P) := by
    rw [hP]; exact ModularCurve.intCoeffs_minpoly_lambdaNModC_coeff q hq2 k
  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨z, hz⟩ := ModularCurve.aeval_lambdaModC_intCoeffs_descent P hint n
    exact ⟨z, by rw [hz]; rfl⟩
  obtain ⟨Pz, hPz⟩ := (Polynomial.mem_lifts P).mp hlift
  exact ⟨Pz, by rw [hPz, hP]⟩

def Pz (hq2 : q ≠ 2) (k : ℕ) : Polynomial ℤ := Classical.choose (exists_intPoly q hq2 k)

theorem aeval_Pz (hq2 : q ≠ 2) (k : ℕ) : aeval (lambdaModC ℚ) ((Pz q hq2 k).map (Int.castRingHom ℚ)) = ((m q).coeff k : L) :=
  Classical.choose_spec (exists_intPoly q hq2 k)

theorem Pz_top (hq2 : q ≠ 2) : Pz q hq2 (q + 1) = 1 := by
  have h := aeval_Pz q hq2 (q + 1)
  have hc : (m q).coeff (q + 1) = 1 := by
    have := (monic_m q hq2).coeff_natDegree
    rwa [natDegree_m q hq2] at this
  rw [hc] at h
  have h1 : (Pz q hq2 (q + 1)).map (Int.castRingHom ℚ) = 1 := by
    apply aeval_mu_injective
    rw [h, map_one]; rfl
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [h1, Polynomial.map_one]

def Psi (hq2 : q ≠ 2) : Polynomial (Polynomial ℤ) := ∑ k ∈ Finset.range (q + 2), C (Pz q hq2 k) * X ^ k

theorem Psi_eq (hq2 : q ≠ 2) : Psi q hq2 = X ^ (q + 1) + ∑ k ∈ Finset.range (q + 1), C (Pz q hq2 k) * X ^ k := by
  rw [Psi, Finset.sum_range_succ, Pz_top, map_one, one_mul, add_comm]

theorem degree_lower_lt (hq2 : q ≠ 2) : (∑ k ∈ Finset.range (q + 1), C (Pz q hq2 k) * X ^ k).degree < ((q + 1 : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine lt_of_le_of_lt (Finset.sup_le (fun b hb => (Polynomial.degree_C_mul_X_pow_le b _).trans
    (WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hb))))) ?_
  exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self q)

theorem Psi_monic (hq2 : q ≠ 2) : (Psi q hq2).Monic := by
  rw [Psi_eq]; exact Polynomial.monic_X_pow_add (degree_lower_lt q hq2)

theorem Psi_natDegree (hq2 : q ≠ 2) : (Psi q hq2).natDegree = q + 1 := by
  rw [Psi_eq, Polynomial.natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]; exact degree_lower_lt q hq2

theorem laurentMap_evalAtLambdaInt (P : Polynomial ℤ) :
    ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) P = aeval (lambdaModC ℚ) (P.map (Int.castRingHom ℚ)) := by
  have h : (laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt
      = (aeval (R := ℚ) (lambdaModC ℚ)).toRingHom.comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtLambdaInt_X, lambdaModC]
  exact congrArg (fun φ => φ P) h

theorem Psi_eval (hq2 : q ≠ 2) : (Psi q hq2).eval₂ ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) (lambdaNModC ℚ q) = 0 := by
  rw [Psi, Polynomial.eval₂_finset_sum]
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow, laurentMap_evalAtLambdaInt, aeval_Pz]

  have h0 : aeval (lambdaNModC ℚ q) ((m q).map (algebraMap Fμ L)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval Fμ _
  have hdeg : ((m q).map (algebraMap Fμ L)).natDegree < q + 2 := by
    rw [Polynomial.natDegree_map, natDegree_m q hq2]; omega
  rw [Polynomial.aeval_eq_sum_range' hdeg] at h0
  simp only [Polynomial.coeff_map, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] at h0
  convert h0 using 2 with k hk <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _

def packet (hq2 : q ≠ 2) : LambdaModularPolynomialData q where
  Ψ := Psi q hq2
  monic := Psi_monic q hq2
  natDegree_eq := Psi_natDegree q hq2
  eval_eq_zero := Psi_eval q hq2

end LambdaPacketSol
end

theorem solution (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    Nonempty (LambdaModularPolynomialData q) :=
  ⟨LambdaPacketSol.packet q hq2⟩

end S_ModularCurve_nonempty_lambdaModularPolynomialData
end P2MW
export P2MW.S_ModularCurve_nonempty_lambdaModularPolynomialData (solution)
