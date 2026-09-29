-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5a076c74-484c-5247-b757-63f694ffe105

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve CongruenceSubgroup

namespace BRIDGE

section A4

variable {K A : Type*} [Field K] [Field A] [Algebra K A]

theorem adjoin_simple_eq_comap (E : IntermediateField K A) (x : E) :
    IntermediateField.adjoin K ({x} : Set E) =
      (IntermediateField.adjoin K ({(x : A)} : Set A)).comap (IntermediateField.val E) := by
  apply IntermediateField.lift_injective
  erw [IntermediateField.lift_adjoin_simple]
  change _ = ((IntermediateField.adjoin K ({(x : A)} : Set A)).comap E.val).map E.val
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left.mpr]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr x.2)

theorem finrank_adjoin_simple_eq_relfinrank (E : IntermediateField K A) (x : E) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set E)) E =
      IntermediateField.relfinrank (IntermediateField.adjoin K ({(x : A)} : Set A)) E := by
  rw [adjoin_simple_eq_comap, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

end A4

theorem coeffEmb_rat_apply (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext k
  rw [coeffEmb_coeff]
  rfl

theorem laurentBaseChange_rat (F : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange ℚ F = F := by
  have himg : (⇑(coeffEmb ℚ) '' (F : Set (LaurentSeries ℚ))) = (F : Set (LaurentSeries ℚ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; rwa [coeffEmb_rat_apply]
    · intro hx; exact ⟨x, hx, coeffEmb_rat_apply x⟩
  rw [laurentBaseChange, himg]
  apply le_antisymm
  · exact IntermediateField.adjoin_le_iff.mpr subset_rfl
  · intro x hx
    exact IntermediateField.subset_adjoin ℚ _ hx

theorem T_mem_Gamma0 (M : ℕ) : ModularGroup.T ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [ModularGroup.T]

end BRIDGE

open BRIDGE in
theorem solution (M : ℕ) [NeZero M] :
    qExpFunctionFieldC ℚ (Gamma0 M) = modularFunctionFieldFull M := by

  set F : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Gamma0 M) with hF
  have hEC : modularFunctionFieldFullC ℚ M = modularFunctionFieldFull M := modularFunctionFieldFullC_rat M
  have hEF : modularFunctionFieldFull M ≤ F := by
    rw [← hEC]; exact modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M
  let A : IntermediateField ℚ (LaurentSeries ℚ) := IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ))
  have hjE : jqModC ℚ ∈ modularFunctionFieldFull M := hEC ▸ jqModC_mem_full ℚ M
  have hAE : A ≤ modularFunctionFieldFull M :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjE)
  have hAF : A ≤ F := hAE.trans hEF

  have h1 : IntermediateField.relfinrank A (modularFunctionFieldFull M) = dedekindPsi M := by
    have h := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi ℚ M
      (by exact_mod_cast (NeZero.ne M))
    have e1 := finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldFullC ℚ M)
      ⟨jqModC ℚ, jqModC_mem_full ℚ M⟩
    rw [← hEC]
    exact e1.symm.trans h

  have hself : laurentBaseChange ℚ F = F := laurentBaseChange_rat F
  have hjF' : jqModC ℚ ∈ laurentBaseChange ℚ F := by rw [hself]; exact hAF (IntermediateField.mem_adjoin_simple_self ℚ _)
  let y : ↥(laurentBaseChange ℚ F) := ⟨jqModC ℚ, hjF'⟩
  have hy : (y : LaurentSeries ℚ) = jqModC ℚ := rfl
  have h2raw := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index ℚ (Gamma0 M)
    (T_mem_Gamma0 M) (Gamma0 M) le_rfl (fun γ hγ => Or.inl hγ) y hy
  have hfin0 :=
    finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (Gamma0 M) (T_mem_Gamma0 M) ℚ
      (laurentBaseChange ℚ F) rfl y (by rw [hy, ← jqModC_rat]; exact (coeffEmb_rat_apply _).symm)
  haveI hfin : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({y} : Set ↥(laurentBaseChange ℚ F)))
      ↥(laurentBaseChange ℚ F) := by convert hfin0 <;> exact Subsingleton.elim _ _
  have h2 : IntermediateField.relfinrank A F ≤ dedekindPsi M := by
    have e2 := finrank_adjoin_simple_eq_relfinrank (laurentBaseChange ℚ F) y
    have h : IntermediateField.relfinrank A (laurentBaseChange ℚ F) ≤ (Gamma0 M).index := e2.symm.trans_le h2raw
    rwa [hself, Gamma0_index] at h
  have h2ne : IntermediateField.relfinrank A F ≠ 0 := by
    have hpos : 0 < Module.finrank ↥(IntermediateField.adjoin ℚ ({y} : Set ↥(laurentBaseChange ℚ F)))
        ↥(laurentBaseChange ℚ F) := Module.finrank_pos
    have e2 := finrank_adjoin_simple_eq_relfinrank (laurentBaseChange ℚ F) y
    have hpos' : 0 < IntermediateField.relfinrank A (laurentBaseChange ℚ F) := by
      rw [← e2]; convert hpos <;> exact Subsingleton.elim _ _
    rw [hself] at hpos'
    exact Nat.pos_iff_ne_zero.mp hpos'

  have htower := IntermediateField.relfinrank_mul_relfinrank hAE hEF
  rw [h1] at htower
  have hψr : dedekindPsi M * IntermediateField.relfinrank (modularFunctionFieldFull M) F ≠ 0 := by
    rw [htower]; exact h2ne
  have hψ : 0 < dedekindPsi M := Nat.pos_of_ne_zero (fun h => hψr (by rw [h, zero_mul]))
  have hr1 : IntermediateField.relfinrank (modularFunctionFieldFull M) F ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left _ hψ
    rw [mul_one, htower]; exact h2
  have hr0 : IntermediateField.relfinrank (modularFunctionFieldFull M) F ≠ 0 :=
    fun h => hψr (by rw [h, mul_zero])
  have hr : IntermediateField.relfinrank (modularFunctionFieldFull M) F = 1 := by omega
  exact le_antisymm (IntermediateField.relfinrank_eq_one_iff.mp hr) hEF

end S_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull (solution)
