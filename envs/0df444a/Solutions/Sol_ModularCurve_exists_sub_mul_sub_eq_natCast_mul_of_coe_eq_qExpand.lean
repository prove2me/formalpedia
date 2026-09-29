-- Prove2me | solution 1 for ModularCurve.exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/aa7b999e-535b-5094-9ff7-3fe31371ff60

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
open ModularCurve Polynomial

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(modularFunctionFieldFull p))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq) :
    ∃ w ∈ Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), jp} : Set ↥(modularFunctionFieldFull p)),
      ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p - jp) *
          ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) - jp ^ p) =
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) * w := by
  classical

  let ι : ↥(modularFunctionFieldFull p) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (coeffEmb (AlgebraicClosure ℚ)).comp (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ))
  have hιj : ι (IgusaScheme.jFull p) = jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = _
    rw [IgusaScheme.coe_jFull, coeffEmb_jq]

  have hcast : ∀ (m n : ℕ) [NeZero m] [NeZero n], m = n →
      jqNModC (AlgebraicClosure ℚ) m = jqNModC (AlgebraicClosure ℚ) n := by
    intro m n _ _ h
    subst h
    rfl
  have hιjp : ι jp = jqNModC (AlgebraicClosure ℚ) (1 * p) := by
    show coeffEmb (AlgebraicClosure ℚ) ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = _
    rw [hjp, coeffEmb_qExpand, coeffEmb_jq, hcast (1 * p) p (one_mul p)]
    rfl

  let R : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
    (Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), jp} :
      Set ↥(modularFunctionFieldFull p))).toSubring.map ι
  have hjA : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈
      Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), jp} : Set ↥(modularFunctionFieldFull p)) :=
    Algebra.subset_adjoin (Set.mem_insert _ _)
  have hjpA : jp ∈
      Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), jp} : Set ↥(modularFunctionFieldFull p)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton jp))
  have hj : jqModC (AlgebraicClosure ℚ) ∈ R := Subring.mem_map.mpr ⟨_, hjA, hιj⟩
  have hjq : jqNModC (AlgebraicClosure ℚ) (1 * p) ∈ R := Subring.mem_map.mpr ⟨_, hjpA, hιjp⟩

  have hK := sub_mul_sub_mem_span_natCast_of_jqModC_mem_of_jqNModC_mem p R hj hjq
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hK
  obtain ⟨w, hw, hιw⟩ := Subring.mem_map.mp a.2
  refine ⟨w, hw, ι.injective ?_⟩
  have ha' := congrArg R.subtype ha
  rw [map_mul, map_natCast, map_mul, map_sub, map_sub, map_pow, map_pow] at ha'
  rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_mul, map_natCast, hιj, hιjp, hιw]

  exact ha'.symm.trans (mul_comm _ _)

end S_ModularCurve_exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand
end P2MW
export P2MW.S_ModularCurve_exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand (solution)
