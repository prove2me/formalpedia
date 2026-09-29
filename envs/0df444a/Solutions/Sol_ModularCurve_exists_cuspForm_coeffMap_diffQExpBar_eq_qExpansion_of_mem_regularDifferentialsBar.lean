-- Prove2me | solution 1 for ModularCurve.exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/58538eff-0347-5df8-bfc7-7e524e1fd05e

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar
import Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_of_isIntegral
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_theta_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.cuspCount_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero"

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace C2primeGlue

variable (N : ℕ) [NeZero N]

abbrev jB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem coeffMap_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : LaurentSeries R) :
    coeffMap f (qEuler R s) = qEuler S (coeffMap f s) := by
  ext n
  simp [qEuler_coeff, coeffMap_coeff]

theorem qEuler_eq_thetaL (s : LaurentSeries ℂ) : qEuler ℂ s = thetaL ℂ s := by
  ext n
  rw [qEuler_coeff, thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

theorem ringHom_rat_eq (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    ι₀.comp (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ ℂ :=
  Subsingleton.elim _ _

theorem coeffMap_coeffEmb' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap, ringHom_rat_eq]

theorem coeffMap_algebraMap' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    coeffMap ι₀ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_laurentBaseChange_complex (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
    coeffMap ι₀ x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange ℂ (modularFunctionFieldFull N)).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) : modularFunctionFieldBar N →+* LaurentSeries ℂ :=
  (coeffMap ι₀).comp (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toSubfield.subtype

theorem phi_apply (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : modularFunctionFieldBar N) :
    phi N ι₀ x = coeffMap ι₀ (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem phi_algebraMap (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi N ι₀ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [phi_apply]
  exact coeffMap_algebraMap' ι₀ c

theorem phi_jB (ι₀ : AlgebraicClosure ℚ →+* ℂ) : phi N ι₀ (jB N) = coeffEmb ℂ jq := by
  rw [phi_apply]
  exact coeffMap_coeffEmb' ι₀ jq

theorem isIntegral_phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) (a : modularFunctionFieldBar N)
    {y : modularFunctionFieldBar N}
    (hy : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N))) y) :
    IsIntegral (Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ))) (phi N ι₀ y) := by
  have hmem : ∀ r : modularFunctionFieldBar N,
      r ∈ Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N)) →
      phi N ι₀ r ∈ Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap c =>
        rw [phi_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
    | add r s _ _ hr hs => rw [map_add]; exact add_mem hr hs
    | mul r s _ _ hr hs => rw [map_mul]; exact mul_mem hr hs
  let ψ : Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N)) →+*
      Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ)) :=
    ((phi N ι₀).comp (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (modularFunctionFieldBar N))).val.toRingHom).codRestrict
      (Algebra.adjoin ℂ ({phi N ι₀ a} : Set (LaurentSeries ℂ))) (fun r => hmem r r.2)
  refine IsIntegral.map_of_comp_eq ψ (phi N ι₀) ?_ hy
  ext r
  rfl

theorem D_jB_ne_zero : D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jB N) ≠ 0 := by
  intro h
  have h1 : diffQExp (modularFunctionFieldBar N) (D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jB N)) =
      qEuler (AlgebraicClosure ℚ) ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) :=
    diffQExp_D _ _
  rw [h, map_zero] at h1
  have h2 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff (-1)) h1
  simp only at h2
  rw [qEuler_coeff] at h2
  have h3 : ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h3, HahnSeries.coeff_zero] at h2
  norm_num at h2

end C2primeGlue

open C2primeGlue in
theorem solution (N : ℕ) [NeZero N] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hω : ω ∈ ModularCurve.regularDifferentialsBar N) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExpBar N ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_modularFunctionFieldBar N

  have hrank : Module.finrank (modularFunctionFieldBar N)
      Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] = 1 := IsCurveOver.finrank_kaehler
  obtain ⟨x, hx⟩ := (finrank_eq_one_iff_of_nonzero'
    (D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jB N)) (D_jB_ne_zero N)).mp hrank ω

  have hxreg : x • D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jB N) ∈ regularDifferentialsBar N := by
    rw [hx]; exact hω
  obtain ⟨h₁, h₂⟩ :=
    ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar N x hxreg

  have hXmem : phi N ι₀ x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N) :=
    coeffMap_mem_laurentBaseChange_complex N ι₀ x.2
  have hJ : phi N ι₀ (jB N) = coeffEmb ℂ jq := phi_jB N ι₀
  have h1728 : phi N ι₀ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) =
      algebraMap ℂ (LaurentSeries ℂ) 1728 := by
    rw [phi_algebraMap, map_ofNat]
  have h₁' := isIntegral_phi N ι₀ (jB N) h₁
  have h₂' := isIntegral_phi N ι₀ ((jB N)⁻¹) h₂
  rw [map_inv₀, hJ] at h₂'
  rw [hJ] at h₁'
  simp only [map_mul, map_pow, map_sub, hJ, h1728] at h₁' h₂'

  obtain ⟨f, hf⟩ := ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_of_isIntegral N (phi N ι₀ x) hXmem
    (dedekindPsi N) h₁' h₂'
  refine ⟨f, ?_⟩

  have hΘ : ModularCurve.diffQExpBar N ω =
      ((x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) *
        qEuler (AlgebraicClosure ℚ) ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← hx]
    exact diffQExp_smul_D _ _ _
  rw [hf, hΘ, map_mul, coeffMap_qEuler, qEuler_eq_thetaL, ← phi_apply, ← phi_apply, hJ]

end

end S_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
end P2MW
export P2MW.S_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar (solution)
