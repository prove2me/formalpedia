-- Prove2me | solution 1 for ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/68d43b02-260b-577e-a68d-97bec9efd490

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option maxHeartbeats 6400000

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC ModularPolynomialData minpoly_jqNModC_eq nonempty_modularPolynomialData_of_squarefree"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval coeffSubring fieldOver jRing jIntegralClosure"
p2m_open "ModularCurve.NodeLocalized"
namespace JMem

noncomputable section
p2m_open "ModularCurve.CharPReduction"

section Vocab

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring_iff' {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem algebraMap_mem_fieldOver' (N : ℕ) [NeZero N] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jqModC_mem_fieldOver' (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem jqNModC_mem_fieldOver'' (N : ℕ) [NeZero N] : jqNModC (AlgebraicClosure ℚ) N ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem jqModC_mem_jRing'' : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing' (a : ↥(coeffSubring A K)) :
    constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem modularEval_mem_fieldOver' (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      exact algebraMap_mem_fieldOver' K N ((mem_coeffSubring_iff' A K).mp c.2).2
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]; refine mul_mem hp ?_
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact jqModC_mem_fieldOver' K N
      · exact jqNModC_mem_fieldOver'' K N

theorem isIntegral_jRing_jqNModC'' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) N) := by
  let jR : ↥(jRing A K) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jRing'' A K⟩
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(jRing A K)) jR), data.monic.map _, ?_⟩
  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  have h0 : Polynomial.aeval (jqNModC (AlgebraicClosure ℚ) N) (minpoly ↥F (jqNModC (AlgebraicClosure ℚ) N)) = 0 :=
    minpoly.aeval ↥F _
  rw [ModularCurve.minpoly_jqNModC_eq (AlgebraicClosure ℚ) N data, Polynomial.aeval_def,
    Polynomial.eval₂_map] at h0
  rw [Polynomial.eval₂_map]
  convert h0 using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [jR]
  rfl

theorem isIntegral_jRing_modularEval' (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    IsIntegral ↥(jRing A K) (modularEval N (coeffSubring A K) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
      exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, constSeries_mem_jRing' A K c⟩)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul]; refine hp.mul ?_
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, jqModC_mem_jRing'' A K⟩)
      · exact isIntegral_jRing_jqNModC'' A K N data

theorem modularEval_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) s ∈ jIntegralClosure (1 * q) A K := by
  have hq : q.Prime := Fact.out
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData_of_squarefree (1 * q)
    (by rw [one_mul]; exact hq.squarefree) (by rw [one_mul]; exact hq.one_lt)
  exact ⟨modularEval_mem_fieldOver' A K (1 * q) s, isIntegral_jRing_modularEval' A K (1 * q) data s⟩

end Vocab

end

end JMem
end NodeLocalized
end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem.ModularCurve.NodeLocalized"

theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jqModC (AlgebraicClosure ℚ) ∈ jIntegralClosure (1 * q) A K ∧
      jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨?_, ?_⟩
  · have := JMem.modularEval_mem_jIntegralClosure A K (q := q) (MvPolynomial.X 0)
    unfold modularEval at this; rw [MvPolynomial.eval₂Hom_X'] at this; exact this
  · have := JMem.modularEval_mem_jIntegralClosure A K (q := q) (MvPolynomial.X 1)
    unfold modularEval at this; rw [MvPolynomial.eval₂Hom_X'] at this; exact this

end S_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem (solution)
