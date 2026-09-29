-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentChart_snd_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e18593a9-b7d7-57f3-b5a5-a2f4be774959

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_hasValue_of_mem_smoothLocalRingSnd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

namespace ChartSndN

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Classical

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

local notation "Qb" => AlgebraicClosure ℚ

def restrictConstants {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F] [Algebra κ F]
    (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) (v : Place k F) : Place κ F where
  toValuationSubring := v.toValuationSubring
  algebraMap_mem' c := by rw [hσ]; exact v.algebraMap_mem' (σ c)
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

theorem restrictConstants_injective {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F]
    [Algebra κ F] (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) :
    Function.Injective (restrictConstants σ hσ) := by
  intro v w h
  have : (restrictConstants σ hσ v).toValuationSubring = (restrictConstants σ hσ w).toValuationSubring := by rw [h]
  exact Place.ext this

theorem restrictConstants_surjective {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra k F]
    [Algebra κ F] (σ : κ →+* k) (hσ : ∀ c, algebraMap κ F c = algebraMap k F (σ c)) (hsurj : Function.Surjective σ) :
    Function.Surjective (restrictConstants σ hσ) := by
  intro w
  refine ⟨{ toValuationSubring := w.toValuationSubring
            algebraMap_mem' := fun c => by obtain ⟨c', rfl⟩ := hsurj c; rw [← hσ]; exact w.algebraMap_mem' c'
            ne_top' := w.ne_top'
            isPrincipalIdealRing' := w.isPrincipalIdealRing' }, ?_⟩
  exact Place.ext rfl

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem redBar_bijective' : Function.Bijective R.redBar := by
  refine ⟨R.redBar.injective, fun c => ?_⟩
  obtain ⟨a, rfl⟩ := P.red_surjective_of_level c
  exact ⟨IsLocalRing.residue A a, R.redBar_residue a⟩

theorem coeffMap_algebraMap_of_ringHom {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_modularFunctionFieldC_of_ringHom {K K' : Type*} [Field K] [Field K'] (σ : K →+* K')
    (M : ℕ) [NeZero M] {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldC K M) :
    coeffMap σ x ∈ modularFunctionFieldC K' M := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      {jqModC K, jqNModC K M}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap_of_ringHom]
        exact (modularFunctionFieldC K' M).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffSemilinearAut.coeffMap_jqModC]
          exact jqModC_mem K' M
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [coeffSemilinearAut.coeffMap_jqNModC]
          exact jqNModC_mem K' M
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

theorem iota_bijective' : Function.Bijective R.ι := by
  have hbij := redBar_bijective' R
  set e : IsLocalRing.ResidueField A ≃+* k := RingEquiv.ofBijective R.redBar hbij with he
  have he_apply : ∀ c, e c = R.redBar c := fun c => rfl
  refine ⟨R.ι.injective, fun g => ?_⟩
  have hmem : coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k) ∈
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N :=
    modularFunctionFieldC_le_full (IsLocalRing.ResidueField A) N
      (coeffMap_mem_modularFunctionFieldC_of_ringHom _ N g.2)
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [R.ι_coe]
  change coeffMap R.redBar (coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k))
      = (g : LaurentSeries k)
  rw [coeffMap_coeffMap,
    coeffMap_congr (g := RingHom.id _) (RingHom.ext fun a => by
      change R.redBar (e.symm a) = a
      rw [← he_apply]; exact e.apply_symm_apply a) _, coeffMap_id]

def algebraResidueField : Algebra (ResidueField A) (modularFunctionFieldC k N) :=
  ((algebraMap k (modularFunctionFieldC k N)).comp R.redBar).toAlgebra

def rc (v : Place k (modularFunctionFieldC k N)) :
    letI := algebraResidueField R; Place (ResidueField A) (modularFunctionFieldC k N) :=
  letI := algebraResidueField R; restrictConstants R.redBar (fun _ => rfl) v

theorem rc_injective : Function.Injective (rc R) := by
  letI := algebraResidueField R
  exact restrictConstants_injective R.redBar (fun _ => rfl)

theorem rc_surjective : Function.Surjective (rc R) := by
  letI := algebraResidueField R
  exact restrictConstants_surjective R.redBar (fun _ => rfl) (redBar_bijective' R).2

theorem rc_toValuationSubring (v : Place k (modularFunctionFieldC k N)) :
    letI := algebraResidueField R; (rc R v).toValuationSubring = v.toValuationSubring := rfl

theorem ord_rc (v : Place k (modularFunctionFieldC k N)) (g : (modularFunctionFieldC k N)) :
    letI := algebraResidueField R; (rc R v).ord g = v.ord g := rfl

theorem iota_algebraMap (x : ResidueField A) :
    letI := algebraResidueField R
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) x)
      = algebraMap (ResidueField A) ↥(modularFunctionFieldC k N) x := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem algebraMap_rc_residueField (v : Place k (modularFunctionFieldC k N)) (x : ResidueField A) :
    letI := algebraResidueField R
    algebraMap (ResidueField A) (rc R v).ResidueField x = algebraMap k v.ResidueField (R.redBar x) := by
  letI := algebraResidueField R
  rw [← (rc R v).residue_algebraMap x, ← v.residue_algebraMap (R.redBar x)]
  rfl

noncomputable def fixedPlaces (P : PlaceSpecialization A q N data hKr k red hα hβ) :
    Finset (Place k (modularFunctionFieldC k N)) :=
  (ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self k N data hKr).toFinset

theorem mem_fixedPlaces_iff (v : Place k (modularFunctionFieldC k N)) :
    v ∈ fixedPlaces P ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v := by
  rw [fixedPlaces, Set.Finite.mem_toFinset]; rfl

set_option maxHeartbeats 6400000 in
noncomputable def chartSnd (hqN : ¬ q ∣ N) (hR : R.IsModel) :
    letI := algebraResidueField R; ComponentChart A (modularFunctionFieldBar (N * q)) (modularFunctionFieldC k N) := by
  letI := algebraResidueField R
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  exact
  { integers := R.R₂.integers
    residue := R.residue₂
    dom := {V | P.IsStrictSnd V}
    nodes := (fixedPlaces P).image (rc R)
    placeMap := fun V => rc R (P.reduceSnd V)
    algebraMap_mem_iff := R.R₂.algebraMap_mem_iff
    residue_surjective := (iota_bijective' R).2.comp R.R₂.residue_surjective
    ker_residue := by
      rw [← R.R₂.ker_residue]
      ext x
      simp only [RingHom.mem_ker, residue₂_apply, map_eq_zero_iff _ (iota_bijective' R).1]
    residue_algebraMap := fun a => by
      rw [residue₂_apply, R.R₂.residue_algebraMap]
      exact iota_algebraMap R _
    exists_smul_mem := fun f hf => by
      obtain ⟨c, h, hres⟩ := R.R₂.exists_smul_mem f hf
      exact ⟨c, h, fun h0 => hres ((map_eq_zero_iff _ (iota_bijective' R).1).mp h0)⟩
    placeMap_not_mem_nodes := fun V hV hn => by
      obtain ⟨v, hv, hvV⟩ := Finset.mem_image.mp hn
      have hvv : v = P.reduceSnd V := rc_injective R hvV
      rw [mem_fixedPlaces_iff] at hv
      exact hV.2 (hvv ▸ hv)
    pointwise := fun V hV _ f hf hfib => by
      have hr : f ∈ R.smoothLocalRingSnd (P.reduceSnd V) := by
        rw [R.mem_smoothLocalRingSnd_iff]
        exact ⟨hf, fun W hW hWV => hfib W hW (by show rc R (P.reduceSnd W) = rc R (P.reduceSnd V); rw [hWV])⟩
      obtain ⟨c, hc, hv⟩ := hR.exists_hasValue_of_mem_smoothLocalRingSnd hqN hV f hf hr
      have hev : V.evalAt f = (c : AlgebraicClosure ℚ) := by
        rw [V.evalAt_of_mem hc.mem, hc.residue_eq, Place.residueInv_algebraMap]
      have hcA : V.evalAt f ∈ A := hev ▸ c.2
      refine ⟨hv.mem, hcA, ?_⟩
      have hcc : (⟨V.evalAt f, hcA⟩ : ↥A) = c := Subtype.ext hev
      rw [hcc, algebraMap_rc_residueField, R.redBar_residue]
      exact hv.residue_eq.symm
    mapDomain_placeMap := fun f hres D hD hD0 Q hQ => by
      obtain ⟨v, rfl⟩ := rc_surjective R Q
      have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v := by
        intro h
        exact hQ (Finset.mem_image.mpr ⟨v, (mem_fixedPlaces_iff v).mpr h, rfl⟩)
      have hres₁ : R.R₂.residue f ≠ 0 := fun h0 => hres (by rw [residue₂_apply, h0, map_zero])
      have hf0 : (f : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
        intro h; apply hres₁
        have : f = 0 := Subtype.ext h
        rw [this, map_zero]
      obtain ⟨D', hD', -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (f : ↥(modularFunctionFieldBar (N * q))) hf0
      have hlaw := ProlongationTuple.divisorLawSnd_oneSided hqN P R hR f.1 f.2 hres₁ D' hD' v hfix
      have hDD : D = D'.filter P.IsStrictSnd := by
        ext W
        rw [Finsupp.filter_apply]
        by_cases hW : P.IsStrictSnd W
        · rw [if_pos hW, hD W hW, hD' W]
        · rw [if_neg hW, hD0 W hW]
      have hcomp : (fun V => rc R (P.reduceSnd V)) = rc R ∘ P.reduceSnd := rfl
      rw [hcomp, Finsupp.mapDomain_comp, Finsupp.mapDomain_apply (rc_injective R), hDD, hlaw]
      rfl }

theorem rc_mem_nodes_iff (hqN : ¬ q ∣ N) (hR : R.IsModel) (v : Place k (modularFunctionFieldC k N)) :
    letI := algebraResidueField R
    rc R v ∈ (chartSnd R hqN hR).nodes ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v := by
  letI := algebraResidueField R
  show rc R v ∈ (fixedPlaces P).image (rc R) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v', hv', hvv'⟩
    rw [rc_injective R hvv'] at hv'
    exact (mem_fixedPlaces_iff v).mp hv'
  · intro hv
    exact ⟨v, (mem_fixedPlaces_iff v).mpr hv, rfl⟩

end ChartSndN

end

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (R : ProlongationTuple P) (hR : R.IsModel) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∃ (C : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N))
      (rc : Place k ↥(modularFunctionFieldC k N) → Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N)),
      Function.Bijective rc ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), (rc v).toValuationSubring = v.toValuationSubring) ∧
      (∀ (v : Place k ↥(modularFunctionFieldC k N)) (g : ↥(modularFunctionFieldC k N)), (rc v).ord g = v.ord g) ∧
      C.integers = R.R₂.integers ∧
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C.integers) (h : f ∈ R.R₂.integers),
        C.residue ⟨f, hC⟩ = R.residue₂ ⟨f, h⟩) ∧
      C.dom = {V | P.IsStrictSnd V} ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N),
        rc v ∈ C.nodes ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), C.placeMap V = rc (P.reduceSnd V)) := by
  letI := ChartSndN.algebraResidueField R
  refine ⟨ChartSndN.chartSnd R hqN hR, ChartSndN.rc R, ⟨ChartSndN.rc_injective R, ChartSndN.rc_surjective R⟩,
    fun v => rfl, fun v g => rfl, rfl, fun f hC h => rfl, rfl, fun v => ChartSndN.rc_mem_nodes_iff R hqN hR v, fun V => rfl⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentChart_snd_of_isModel (solution)
