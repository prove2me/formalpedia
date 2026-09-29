-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2b8c28a3-2247-5279-9d2b-88478dd1b380

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable scoped instance (priority := high) AnnulusG1Hat.instAlgebraResidueFieldFullC
    {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ) :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  SubalgebraClass.toAlgebra (modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)

namespace AnnulusG1Hat

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

section Core

variable (R : ProlongationTuple P) [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
  [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]

theorem core (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u) (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (θ : MvPowerSeries (Fin 2) W →+*
      AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hθ : Function.Surjective θ)
    (hθπ : θ (MvPowerSeries.C π) = algebraMap _ _ (R.nodeConst K w ϖ))
    (hθ0 : θ (MvPowerSeries.X 0) = algebraMap _ _ c.x) (hθ1 : θ (MvPowerSeries.X 1) = algebraMap _ _ c.y)
    (hdim : 2 ≤ ringKrullDim (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) :
    ∃ (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E)) (α : UVCrossingModel W (π ^ E)), IsUnit α ∧
      (∀ o : W, ι (θ (MvPowerSeries.C o)) = const (π ^ E) o) ∧
      ι (algebraMap _ _ c.x) = U (π ^ E) * α ∧ ι (algebraMap _ _ c.y) = V (π ^ E) := by
  let alg := algebraMap ↥(R.nodeIntegersOver K w)
    (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
  have hualg : IsUnit (alg u) := hu.map alg
  have e1 : alg c.x * alg c.y = alg (R.nodeConst K w ϖ) ^ E * alg u :=
    ((map_mul alg c.x c.y).symm.trans (congrArg alg hxy)).trans
      ((map_mul alg _ _).trans (congrArg (· * alg u) (map_pow alg _ E)))
  have hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) =
      θ (MvPowerSeries.C π) ^ E * (hualg.unit : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w))
        ↥(R.nodeIntegersOver K w)) := by
    rw [hθ0, hθ1, hθπ, IsUnit.unit_spec]
    exact e1
  obtain ⟨ι, hWc, hx, hy⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit π hπ E hE θ hθ
      hualg.unit hrel hdim
  refine ⟨ι, ι (hualg.unit : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)),
    (Units.isUnit hualg.unit).map ι, hWc, ?_, ?_⟩
  · exact (congrArg ι hθ0).symm.trans hx
  · exact (congrArg ι hθ1).symm.trans hy

end Core

section OrderReadingFst

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N))

noncomputable def res₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

theorem res₁_apply (b : ↥(R.nodeIntegersOver K w)) : res₁ R K w b = R.nodeResidue₁ w ⟨b, b.2.1⟩ := rfl

def toR₁ : ↥(R.nodeIntegersOver K w) →+* ↥R.R₁.integers where
  toFun v := ⟨v, v.2.1.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem res₁_eq (v : ↥(R.nodeIntegersOver K w)) : res₁ R K w v = R.ι (R.R₁.residue (toR₁ R K w v)) := rfl

theorem not_isUnit_toR₁_nodeConst (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) : ¬ IsUnit (toR₁ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₁ R K w (R.nodeConst K w ϖ) : ↥R.R₁.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₁.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

theorem res₁_nodeConst_eq_zero (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) : res₁ R K w (R.nodeConst K w ϖ) = 0 := by
  have hmem : toR₁ R K w (R.nodeConst K w ϖ) ∈ maximalIdeal ↥R.R₁.integers :=
    (mem_maximalIdeal _).mpr (not_isUnit_toR₁_nodeConst R K w ϖ hϖ)
  rw [← R.R₁.ker_residue, RingHom.mem_ker] at hmem
  rw [res₁_eq, hmem, map_zero]

variable [PerfectField k]

theorem ord_res₁_nonneg [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hw : w ∈ W₀) (f : ↥(R.nodeIntegersOver K w)) (hf : res₁ R K w f ≠ 0) :
    0 ≤ w.ord (res₁ R K w f) :=
  (hreg.1 (f : ↥(modularFunctionFieldBar (N * q))) f.2.1.1 f.2.1.2.1 w
    (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w (hW₀ w hw))
    (hW₀ w hw).2.1
    (fun V hV => R.ord_nonneg_of_mem_nodeIntegers f.2.1 hV)).1 hf

variable (c : R.NodeCoordinates K w)

theorem ord_res₁_eq_zero_of_isUnit
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₁ R K w f ≠ 0 → 0 ≤ w.ord (res₁ R K w f))
    (f : ↥(R.nodeIntegersOver K w)) (hu : IsUnit f) (hf : res₁ R K w f ≠ 0) : w.ord (res₁ R K w f) = 0 := by
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hfg : res₁ R K w f * res₁ R K w g = 1 := by rw [← map_mul, hg, map_one]
  have hg0 : res₁ R K w g ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hfg; exact zero_ne_one hfg
  have h := congrArg w.ord hfg
  rw [w.ord_mul hf hg0, w.ord_one] at h
  have h1 := hord f hf
  have h2 := hord g hg0
  omega

theorem exists_eq_of_mem_span_triple {B : Type*} [CommRing B] (p x y f : B)
    (h : f ∈ Ideal.span ({p, x, y} : Set B)) : ∃ a b g : B, f = a * p + b * x + g * y := by
  rw [Ideal.mem_span_insert] at h
  obtain ⟨a, z, hz, rfl⟩ := h
  rw [Ideal.mem_span_insert] at hz
  obtain ⟨b, z', hz', rfl⟩ := hz
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz'
  exact ⟨a, b, g, by ring⟩

theorem exists_unit_sub_mul_pow_mem (ϖ : ↥(NodeLocalized.coeffSubring A K)) [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₁ R K w f ≠ 0 → 0 ≤ w.ord (res₁ R K w f))
    (hϖ0 : res₁ R K w (R.nodeConst K w ϖ) = 0) (n : ℕ) :
    ∀ f : ↥(R.nodeIntegersOver K w), res₁ R K w f ≠ 0 → w.ord (res₁ R K w f) = (n : ℤ) →
      ∃ g : ↥(R.nodeIntegersOver K w), IsUnit g ∧ f - g * c.y ^ n ∈ Ideal.span {R.nodeConst K w ϖ, c.x} := by
  have hx0 : res₁ R K w c.x = 0 := by rw [res₁_apply]; exact c.x_fst
  have hy1 : w.ord (res₁ R K w c.y) = 1 := by rw [res₁_apply]; exact c.y_fst
  have hy0 : res₁ R K w c.y ≠ 0 := by rw [res₁_apply]; exact c.nodeResidue₁_y_ne_zero

  have step : ∀ f : ↥(R.nodeIntegersOver K w), ¬ IsUnit f → res₁ R K w f ≠ 0 →
      ∃ a b g : ↥(R.nodeIntegersOver K w), f = a * R.nodeConst K w ϖ + b * c.x + g * c.y ∧
        res₁ R K w g ≠ 0 ∧ w.ord (res₁ R K w f) = w.ord (res₁ R K w g) + 1 := by
    intro f hnu hf
    have hfm : f ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := (mem_maximalIdeal _).mpr hnu
    rw [hmaxB] at hfm
    obtain ⟨a, b, g, hfeq⟩ := exists_eq_of_mem_span_triple _ _ _ f hfm
    have hres : res₁ R K w f = res₁ R K w g * res₁ R K w c.y := by
      rw [hfeq, map_add, map_add, map_mul, map_mul, map_mul, hϖ0, hx0, mul_zero, mul_zero, zero_add, zero_add]
    have hg0 : res₁ R K w g ≠ 0 := by
      intro h0; apply hf; rw [hres, h0, zero_mul]
    refine ⟨a, b, g, hfeq, hg0, ?_⟩
    rw [hres, w.ord_mul hg0 hy0, hy1]
  induction n with
  | zero =>
      intro f hf hn
      have hu : IsUnit f := by
        by_contra hnu
        obtain ⟨a, b, g, -, hg0, hordf⟩ := step f hnu hf
        have := hord g hg0
        push_cast at hn
        omega
      exact ⟨f, hu, by rw [pow_zero, mul_one, sub_self]; exact zero_mem _⟩
  | succ n ih =>
      intro f hf hn
      have hnu : ¬ IsUnit f := by
        intro hu
        have := ord_res₁_eq_zero_of_isUnit R K w hord f hu hf
        push_cast at hn
        omega
      obtain ⟨a, b, g, hfeq, hg0, hordf⟩ := step f hnu hf
      have hordg : w.ord (res₁ R K w g) = (n : ℤ) := by push_cast at hn; omega
      obtain ⟨g', hg', hmem⟩ := ih g hg0 hordg
      refine ⟨g', hg', ?_⟩
      have heq : f - g' * c.y ^ (n + 1) =
          a * R.nodeConst K w ϖ + b * c.x + (g - g' * c.y ^ n) * c.y := by
        rw [hfeq]; ring
      rw [heq]
      refine add_mem (add_mem ?_ ?_) (Ideal.mul_mem_right _ _ hmem)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end OrderReadingFst

section ReadFst

variable (R : ProlongationTuple P) [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsLocalRing ↥(R.nodeIntegersOver K w)]

theorem order_reading_fst (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₁ R K w f ≠ 0 → 0 ≤ w.ord (res₁ R K w f))
    (hϖ0 : res₁ R K w (R.nodeConst K w ϖ) = 0)
    {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E)) (α : UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * α) (hιy : ι (algebraMap _ _ c.y) = V (π ^ E))
    (f : ↥(R.nodeIntegersOver K w)) (n : ℕ) (hf : R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0)
    (hn : w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ)) :
    ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
  obtain ⟨g, hg, hmem⟩ := exists_unit_sub_mul_pow_mem R K w c ϖ hmaxB hord hϖ0 n f hf hn
  let φ : ↥(R.nodeIntegersOver K w) →+* UVCrossingModel W (π ^ E) :=
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
      UVCrossingModel W (π ^ E)).comp (algebraMap _ _)
  have hφ : ∀ b, φ b = ι (algebraMap _ _ b) := fun b => rfl
  refine ⟨φ g, hg.map φ, ?_⟩
  have hφf : ι (algebraMap _ _ f) - φ g * V (π ^ E) ^ n = φ (f - g * c.y ^ n) := by
    rw [map_sub, map_mul, map_pow, hφ f, hφ c.y, hιy]
  rw [hφf]
  have hle : Ideal.map φ (Ideal.span {R.nodeConst K w ϖ, c.x}) ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · rw [SetLike.mem_coe, hφ, hιϖ]; exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, hφ, hιx]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact hle (Ideal.mem_map_of_mem φ hmem)

end ReadFst

namespace Snd

section OrderReadingSnd

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N))

noncomputable def res₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
  (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))

theorem res₂_apply (b : ↥(R.nodeIntegersOver K w)) : res₂ R K w b = R.nodeResidue₂ w ⟨b, b.2.1⟩ := rfl

def toR₂ : ↥(R.nodeIntegersOver K w) →+* ↥R.R₂.integers where
  toFun v := ⟨v, v.2.1.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem res₂_eq (v : ↥(R.nodeIntegersOver K w)) : res₂ R K w v = R.ι (R.R₂.residue (toR₂ R K w v)) := rfl

theorem not_isUnit_toR₂_nodeConst (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) : ¬ IsUnit (toR₂ R K w (R.nodeConst K w ϖ)) := by
  set a : A := ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ with ha
  have hred : red a = 0 := hϖ
  have hanu : ¬ IsUnit a := fun hu => by
    have := hu.map red
    rw [hred] at this
    exact not_isUnit_zero this
  have hfval : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := rfl
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : ((toR₂ R K w (R.nodeConst K w ϖ) : ↥R.R₂.integers) : ↥(modularFunctionFieldBar (N * q))) *
      (g : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    rw [← MulMemClass.coe_mul, hg]; rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [hfval, h0, map_zero, zero_mul] at hg'
    exact zero_ne_one hg'
  have hginv : (g : ↥(modularFunctionFieldBar (N * q))) =
      algebraMap (AlgebraicClosure ℚ) _ ((a : AlgebraicClosure ℚ)⁻¹) := by
    rw [map_inv₀, ← hfval]
    exact (eq_inv_of_mul_eq_one_right hg')
  have hmemA : (a : AlgebraicClosure ℚ)⁻¹ ∈ A := by
    have := g.2
    rw [hginv] at this
    exact (R.R₂.algebraMap_mem_iff _).mp this
  exact hanu (isUnit_iff_exists_inv.mpr ⟨⟨(a : AlgebraicClosure ℚ)⁻¹, hmemA⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩)

theorem res₂_nodeConst_eq_zero (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : NodeLocalized.redRestrict red K ϖ = 0) : res₂ R K w (R.nodeConst K w ϖ) = 0 := by
  have hmem : toR₂ R K w (R.nodeConst K w ϖ) ∈ maximalIdeal ↥R.R₂.integers :=
    (mem_maximalIdeal _).mpr (not_isUnit_toR₂_nodeConst R K w ϖ hϖ)
  rw [← R.R₂.ker_residue, RingHom.mem_ker] at hmem
  rw [res₂_eq, hmem, map_zero]

variable [PerfectField k]

theorem ord_res₂_nonneg [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hw : w ∈ W₀) (f : ↥(R.nodeIntegersOver K w)) (hf : res₂ R K w f ≠ 0) :
    0 ≤ (arithFrobC q k N • w).ord (res₂ R K w f) := by
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
  exact (hreg.1 (f : ↥(modularFunctionFieldBar (N * q))) f.2.1.1 f.2.1.2.1 w
    (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w (hW₀ w hw))
    (hW₀ w hw).2.1
    (fun V hV => R.ord_nonneg_of_mem_nodeIntegers f.2.1 hV)).2 hf

variable (c : R.NodeCoordinates K w)

theorem ord_res₂_eq_zero_of_isUnit
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₂ R K w f ≠ 0 → 0 ≤ (arithFrobC q k N • w).ord (res₂ R K w f))
    (f : ↥(R.nodeIntegersOver K w)) (hu : IsUnit f) (hf : res₂ R K w f ≠ 0) : (arithFrobC q k N • w).ord (res₂ R K w f) = 0 := by
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hfg : res₂ R K w f * res₂ R K w g = 1 := by rw [← map_mul, hg, map_one]
  have hg0 : res₂ R K w g ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hfg; exact zero_ne_one hfg
  have h := congrArg (arithFrobC q k N • w).ord hfg
  rw [(arithFrobC q k N • w).ord_mul hf hg0, (arithFrobC q k N • w).ord_one] at h
  have h1 := hord f hf
  have h2 := hord g hg0
  omega

theorem exists_eq_of_mem_span_triple {B : Type*} [CommRing B] (p x y f : B)
    (h : f ∈ Ideal.span ({p, x, y} : Set B)) : ∃ a b g : B, f = a * p + b * x + g * y := by
  rw [Ideal.mem_span_insert] at h
  obtain ⟨a, z, hz, rfl⟩ := h
  rw [Ideal.mem_span_insert] at hz
  obtain ⟨b, z', hz', rfl⟩ := hz
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz'
  exact ⟨a, b, g, by ring⟩

theorem exists_unit_sub_mul_pow_mem (ϖ : ↥(NodeLocalized.coeffSubring A K)) [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₂ R K w f ≠ 0 → 0 ≤ (arithFrobC q k N • w).ord (res₂ R K w f))
    (hϖ0 : res₂ R K w (R.nodeConst K w ϖ) = 0) (n : ℕ) :
    ∀ f : ↥(R.nodeIntegersOver K w), res₂ R K w f ≠ 0 → (arithFrobC q k N • w).ord (res₂ R K w f) = (n : ℤ) →
      ∃ g : ↥(R.nodeIntegersOver K w), IsUnit g ∧ f - g * c.x ^ n ∈ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  have hx0 : res₂ R K w c.y = 0 := by rw [res₂_apply]; exact c.y_snd
  have hy1 : (arithFrobC q k N • w).ord (res₂ R K w c.x) = 1 := by rw [res₂_apply]; exact c.x_snd
  have hy0 : res₂ R K w c.x ≠ 0 := by rw [res₂_apply]; exact c.nodeResidue₂_x_ne_zero

  have step : ∀ f : ↥(R.nodeIntegersOver K w), ¬ IsUnit f → res₂ R K w f ≠ 0 →
      ∃ a b g : ↥(R.nodeIntegersOver K w), f = a * R.nodeConst K w ϖ + b * c.y + g * c.x ∧
        res₂ R K w g ≠ 0 ∧ (arithFrobC q k N • w).ord (res₂ R K w f) = (arithFrobC q k N • w).ord (res₂ R K w g) + 1 := by
    intro f hnu hf
    have hfm : f ∈ maximalIdeal ↥(R.nodeIntegersOver K w) := (mem_maximalIdeal _).mpr hnu
    rw [hmaxB] at hfm
    obtain ⟨a, b, g, hfeq⟩ := exists_eq_of_mem_span_triple _ _ _ f hfm
    have hres : res₂ R K w f = res₂ R K w g * res₂ R K w c.x := by
      rw [hfeq, map_add, map_add, map_mul, map_mul, map_mul, hϖ0, hx0, mul_zero, mul_zero, zero_add, zero_add]
    have hg0 : res₂ R K w g ≠ 0 := by
      intro h0; apply hf; rw [hres, h0, zero_mul]
    refine ⟨a, b, g, hfeq, hg0, ?_⟩
    rw [hres, (arithFrobC q k N • w).ord_mul hg0 hy0, hy1]
  induction n with
  | zero =>
      intro f hf hn
      have hu : IsUnit f := by
        by_contra hnu
        obtain ⟨a, b, g, -, hg0, hordf⟩ := step f hnu hf
        have := hord g hg0
        push_cast at hn
        omega
      exact ⟨f, hu, by rw [pow_zero, mul_one, sub_self]; exact zero_mem _⟩
  | succ n ih =>
      intro f hf hn
      have hnu : ¬ IsUnit f := by
        intro hu
        have := ord_res₂_eq_zero_of_isUnit R K w hord f hu hf
        push_cast at hn
        omega
      obtain ⟨a, b, g, hfeq, hg0, hordf⟩ := step f hnu hf
      have hordg : (arithFrobC q k N • w).ord (res₂ R K w g) = (n : ℤ) := by push_cast at hn; omega
      obtain ⟨g', hg', hmem⟩ := ih g hg0 hordg
      refine ⟨g', hg', ?_⟩
      have heq : f - g' * c.x ^ (n + 1) =
          a * R.nodeConst K w ϖ + b * c.y + (g - g' * c.x ^ n) * c.x := by
        rw [hfeq]; ring
      rw [heq]
      refine add_mem (add_mem ?_ ?_) (Ideal.mul_mem_right _ _ hmem)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end OrderReadingSnd

section ReadSnd

variable (R : ProlongationTuple P) [PerfectField k] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w) [IsLocalRing ↥(R.nodeIntegersOver K w)]

theorem order_reading_snd (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x})
    (hord : ∀ f : ↥(R.nodeIntegersOver K w), res₂ R K w f ≠ 0 → 0 ≤ (arithFrobC q k N • w).ord (res₂ R K w f))
    (hϖ0 : res₂ R K w (R.nodeConst K w ϖ) = 0)
    {W : Type*} [CommRing W] (π : W) (E : ℕ)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E)) (α : UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * α) (hιy : ι (algebraMap _ _ c.y) = V (π ^ E)) (hαu : IsUnit α)
    (f : ↥(R.nodeIntegersOver K w)) (n : ℕ) (hf : R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0)
    (hn : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ)) :
    ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
  obtain ⟨g, hg, hmem⟩ := exists_unit_sub_mul_pow_mem R K w c ϖ hmaxB hord hϖ0 n f hf hn
  let φ : ↥(R.nodeIntegersOver K w) →+* UVCrossingModel W (π ^ E) :=
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
      UVCrossingModel W (π ^ E)).comp (algebraMap _ _)
  have hφ : ∀ b, φ b = ι (algebraMap _ _ b) := fun b => rfl
  refine ⟨φ g * α ^ n, (hg.map φ).mul (hαu.pow n), ?_⟩
  have hφf : ι (algebraMap _ _ f) - φ g * α ^ n * U (π ^ E) ^ n = φ (f - g * c.x ^ n) := by
    rw [map_sub, map_mul, map_pow, hφ f, hφ c.x, hιx, mul_pow, mul_assoc, mul_comm (α ^ n)]
  rw [hφf]
  have hle : Ideal.map φ (Ideal.span {R.nodeConst K w ϖ, c.y}) ≤ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with rfl | rfl
    · rw [SetLike.mem_coe, hφ, hιϖ]; exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [SetLike.mem_coe, hφ, hιy]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact hle (Ideal.mem_map_of_mem φ hmem)

end ReadSnd

end Snd

end AnnulusG1Hat

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (c : R.NodeCoordinates K w)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (θ : MvPowerSeries (Fin 2) W →+*
      AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hθ : Function.Surjective θ)
    (hθπ : θ (MvPowerSeries.C π) = algebraMap _ _ (R.nodeConst K w ϖ))
    (hθ0 : θ (MvPowerSeries.X 0) = algebraMap _ _ c.x) (hθ1 : θ (MvPowerSeries.X 1) = algebraMap _ _ c.y)
    (hdim : 2 ≤ ringKrullDim (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))) :
    ∃ (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E)) (α β : UVCrossingModel W (π ^ E)), IsUnit α ∧ IsUnit β ∧
      (∀ o : W, ι (θ (MvPowerSeries.C o)) = const (π ^ E) o) ∧
      ι (algebraMap _ _ c.x) = U (π ^ E) * α ∧ ι (algebraMap _ _ c.y) = V (π ^ E) * β ∧
      (∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) ∧
      (∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) := by
  have hϖ0' : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hmaxB : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y} :=
    hmax.2 _ (maximalIdeal.isMaximal _)
  have hmaxB' : maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.y, c.x} := by
    rw [hmaxB]
    show Ideal.span (insert _ {c.x, c.y}) = Ideal.span (insert _ {c.y, c.x})
    rw [Set.pair_comm]
  obtain ⟨ι, α, hα, hWc, hιx, hιy⟩ := AnnulusG1Hat.core R K w c ϖ E hE u hu hxy π hπ θ hθ hθπ hθ0 hθ1 hdim
  have hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π := (congrArg ι hθπ).symm.trans (hWc π)
  refine ⟨ι, α, 1, hα, isUnit_one, hWc, hιx, ?_, ?_, ?_⟩
  · rw [mul_one]; exact hιy
  · intro f n hf hn
    exact AnnulusG1Hat.order_reading_fst R K w c ϖ hmaxB
      (fun g hg => AnnulusG1Hat.ord_res₁_nonneg R K w hqN W₀ hW₀ hreg hw g hg)
      (AnnulusG1Hat.res₁_nodeConst_eq_zero R K w ϖ hϖ0') π E ι α hιϖ hιx hιy f n hf hn
  · intro f n hf hn
    exact AnnulusG1Hat.Snd.order_reading_snd R K w c ϖ hmaxB'
      (fun g hg => AnnulusG1Hat.Snd.ord_res₂_nonneg R K w hqN W₀ hW₀ hreg hw g hg)
      (AnnulusG1Hat.Snd.res₂_nodeConst_eq_zero R K w ϖ hϖ0') π E ι α hιϖ hιx hιy hα f n hf hn

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel_of_isMaximal (solution)
