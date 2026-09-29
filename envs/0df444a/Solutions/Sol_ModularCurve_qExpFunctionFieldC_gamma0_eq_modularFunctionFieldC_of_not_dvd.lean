-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0a447b8f-7262-5f3c-992b-0507fc2d1d67

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve IntermediateField

namespace IgusaX0

variable (K : Type*) [Field K] (M : ℕ) [NeZero M]

noncomputable def jF : qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) :=
  ⟨jqModC K, intFormRatiosC_subset K _ (jqModC_mem_intFormRatiosC K _)⟩

theorem coe_jF : ((jF K M : qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) : LaurentSeries K) = jqModC K := rfl

theorem relfinrank_adjoin_eq_finrank :
    (IntermediateField.adjoin K {(jqModC K : LaurentSeries K)}).relfinrank (qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) =
      Module.finrank (IntermediateField.adjoin K ({jF K M} : Set (qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
        (qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by
  set F := qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) with hF
  set E := IntermediateField.adjoin K {(jqModC K : LaurentSeries K)} with hE
  set E' := IntermediateField.adjoin K ({jF K M} : Set F) with hE'
  have hlift : lift E' = E := lift_adjoin_simple K F (jF K M)
  have hEF : E ≤ F := by rw [← hlift]; exact lift_le E'
  rw [relfinrank_eq_finrank_of_le hEF]

  let i : (E' : Type _) ≃+* (E : Type _) :=
    (liftAlgEquiv E').toRingEquiv.trans (IntermediateField.equivOfEq hlift).toRingEquiv
  let j : (F : Type _) ≃+* (extendScalars hEF : Type _) := RingEquiv.refl _
  symm
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  exact RingHom.ext fun x => Subtype.ext rfl

end IgusaX0

theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] [CharP K p] (hpM : ¬ p ∣ M) :
    ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) = ModularCurve.modularFunctionFieldC K M := by
  classical
  set F := qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) with hF
  set F₀ := modularFunctionFieldC K M with hF₀
  set E := IntermediateField.adjoin K {(jqModC K : LaurentSeries K)} with hE

  have hF₀F : F₀ ≤ F := (modularFunctionFieldC_le_full K M).trans (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K M)
  have hEF₀ : E ≤ F₀ := by
    rw [hE, adjoin_simple_le_iff]
    exact jqModC_mem K M

  have hψ : E.relfinrank F₀ = dedekindPsi M :=
    relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi K M p hpM
  obtain ⟨hfin, hle⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
    (CongruenceSubgroup.Gamma0 M) (by
      rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T])
    (CongruenceSubgroup.Gamma0 M) le_rfl (fun γ hγ => Or.inl hγ) (IgusaX0.jF K M) (IgusaX0.coe_jF K M)
  rw [Gamma0_index] at hle
  have hEF : E.relfinrank F ≤ dedekindPsi M := by
    rw [IgusaX0.relfinrank_adjoin_eq_finrank]; exact hle
  have hEF0 : E.relfinrank F ≠ 0 := by
    rw [IgusaX0.relfinrank_adjoin_eq_finrank]
    haveI := hfin
    exact Module.finrank_pos.ne'

  have htower := relfinrank_mul_relfinrank hEF₀ hF₀F
  rw [hψ] at htower
  have hψpos : 0 < dedekindPsi M := by
    refine Nat.pos_of_ne_zero fun h0 => hEF0 ?_
    rw [← htower, h0, zero_mul]
  have h1 : F₀.relfinrank F = 1 := by
    have hle' : dedekindPsi M * F₀.relfinrank F ≤ dedekindPsi M * 1 := by rw [htower, mul_one]; exact hEF
    have hpos : 0 < F₀.relfinrank F := by
      rcases Nat.eq_zero_or_pos (F₀.relfinrank F) with h | h
      · rw [h, mul_zero] at htower; exact absurd htower.symm hEF0
      · exact h
    have := Nat.le_of_mul_le_mul_left hle' hψpos
    omega
  exact le_antisymm (relfinrank_eq_one_iff.mp h1) hF₀F

end S_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd (solution)
