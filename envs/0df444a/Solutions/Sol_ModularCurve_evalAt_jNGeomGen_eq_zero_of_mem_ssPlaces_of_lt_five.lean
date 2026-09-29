-- Prove2me | solution 1 for ModularCurve.evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8e049bcd-42a7-5f75-ab80-7914b475df17

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_j_eq_zero_of_j_eq_zero_of_ringChar
import Theorems.Thm_WeierstrassCurve_fullKernelQuotient_discriminant_ne_zero
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option Elab.async false
set_option autoImplicit false

namespace SecondValueVanishing

open AlgebraicCurve ModularCurve

section Rational

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_sub_evalAt_pos {w : Place K F} (hrat : w.IsRational) {f : F}
    (hf : f ∈ w.toValuationSubring) (hne : f - algebraMap K F (w.evalAt f) ≠ 0) :
    0 < w.ord (f - algebraMap K F (w.evalAt f)) := by
  have hmem : f - algebraMap K F (w.evalAt f) ∈ w.toValuationSubring :=
    sub_mem hf (w.algebraMap_mem' _)
  rcases eq_or_ne (w.ord (f - algebraMap K F (w.evalAt f))) 0 with h0 | h0
  · exfalso
    refine w.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K w.ResidueField (w.evalAt (f - algebraMap K F (w.evalAt f))) = 0 := by
      rw [w.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (w.evalAt f), hmem⟩ : w.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K w.toValuationSubring (w.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (w.evalAt f)
          = f - (algebraMap K w.toValuationSubring (w.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← w.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K w.ResidueField).injective).mp hres
  · have hnonneg := w.ord_nonneg_of_mem hmem
    omega

end Rational

section Identification

variable (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] (N : ℕ) [NeZero N]

private noncomputable def toC (hqN : ¬ q ∣ N) : modularFunctionFieldFullC K N →ₐ[K] modularFunctionFieldC K N :=
  (IntermediateField.equivOfEq (modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN).symm).toAlgHom

private theorem toC_surjective (hqN : ¬ q ∣ N) : Function.Surjective (toC K q N hqN) :=
  (IntermediateField.equivOfEq
    (modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN).symm).surjective

private theorem toC_isIntegral (hqN : ¬ q ∣ N) : (toC K q N hqN).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ (toC_surjective K q N hqN)

private theorem toC_jq (hqN : ¬ q ∣ N) :
    toC K q N hqN ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)
        - algebraMap K (modularFunctionFieldFullC K N) 0) =
      jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0 :=
  Subtype.ext rfl

private theorem toC_jqN (hqN : ¬ q ∣ N) :
    toC K q N hqN ((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N)
        - algebraMap K (modularFunctionFieldFullC K N) 0) =
      jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0 :=
  Subtype.ext rfl

private theorem ramificationIndexAlong_toC (hqN : ¬ q ∣ N) (w : Place K (modularFunctionFieldC K N)) :
    Place.ramificationIndexAlong (toC K q N hqN) w = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : w.ord (π : modularFunctionFieldC K N) = 1 := w.ord_coe_irreducible hπ
  obtain ⟨g, hg⟩ := toC_surjective K q N hqN π
  have h2 := Place.ord_restrictAlong (toC K q N hqN) (toC_isIntegral K q N hqN) w g
  rw [hg, h1] at h2
  exact_mod_cast Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg _) h2.symm

private theorem ord_toC (hqN : ¬ q ∣ N) (w : Place K (modularFunctionFieldC K N)) (g : modularFunctionFieldFullC K N) :
    w.ord (toC K q N hqN g) =
      (w.restrictAlong (toC K q N hqN) (toC_isIntegral K q N hqN)).ord g := by
  rw [Place.ord_restrictAlong (toC K q N hqN) (toC_isIntegral K q N hqN),
    ramificationIndexAlong_toC]
  simp

set_option synthInstance.maxHeartbeats 1600000 in
private theorem finiteAlong_toC (hqN : ¬ q ∣ N) : FiniteAlong K (toC K q N hqN) := by
  unfold FiniteAlong
  letI := algebraAlong (toC K q N hqN)
  exact Module.Finite.of_surjective
    (Algebra.linearMap (modularFunctionFieldFullC K N) (modularFunctionFieldC K N)) (toC_surjective K q N hqN)

private theorem separableAlong_toC (hqN : ¬ q ∣ N) : SeparableAlong K (toC K q N hqN) := by
  unfold SeparableAlong
  letI := algebraAlong (toC K q N hqN)
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := toC_surjective K q N hqN x
  exact isSeparable_algebraMap (K := modularFunctionFieldC K N) y

private theorem restrictAlong_toC_surjective (hqN : ¬ q ∣ N) :
    Function.Surjective (fun w : Place K (modularFunctionFieldC K N) =>
      w.restrictAlong (toC K q N hqN) (toC_isIntegral K q N hqN)) :=
  Place.restrictAlong_surjective (toC K q N hqN) (toC_isIntegral K q N hqN)
    (finiteAlong_toC K q N hqN) (separableAlong_toC K q N hqN)

end Identification

private theorem isRational_full {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ} [NeZero N]
    (v : Place K (modularFunctionFieldFullC K N)) : v.IsRational := by
  haveI : IsCurveOver K (modularFunctionFieldFullC K N) := isCurveOver_modularFunctionFieldFullC K N
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

private theorem _root_.SecondValueVanishing.exists_generator {G : Type*} [AddCommGroup G] {N : ℕ} (H : AddSubgroup G)
    (hH : IsAddCyclic H ∧ Nat.card H = N) :
    ∃ Q : G, H = AddSubgroup.zmultiples Q ∧ addOrderOf Q = N := by
  haveI := hH.1
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := H)
  refine ⟨g, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · intro hx
      exact AddSubgroup.zmultiples_le_of_mem g.2 hx
  · rw [AddSubgroup.addOrderOf_coe, addOrderOf_eq_card_of_forall_mem_zmultiples hg, hH.2]

p2m_export "SecondValueVanishing" "exists_generator"
open WeierstrassCurve in

private theorem evalAt_jNGeomGen_eq_zero {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqN : ¬ q ∣ N) (hchar : ringChar K = 2 ∨ ringChar K = 3)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) (ha : w.evalAt (jGeomGen K N) = 0) :
    w.evalAt (jNGeomGen K N) = 0 := by
  classical
  have hNK : (N : K) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff K q N).mp h)
  have hss : IsSupersingularPlace q N K w := hw
  have hcw := hss.isCentreOf_evalAt
  have hcw1 : 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (w.evalAt (jGeomGen K N))) := hcw.1
  have hposj : 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0) := by
    rw [ha] at hcw1
    exact hcw1

  have hfin := finite_setOf_ord_jGeomGen_sub_pos K N
    (isSeparable_jqNModC_of_natCast_ne_zero K N hNK) 0
  let ρ : Place K (modularFunctionFieldC K N) → Place K (modularFunctionFieldFullC K N) :=
    fun w' => w'.restrictAlong (toC K q N hqN) (toC_isIntegral K q N hqN)
  let S : Finset (Place K (modularFunctionFieldFullC K N)) := hfin.toFinset.image ρ
  have hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) -
      algebraMap K (modularFunctionFieldFullC K N) 0) := by
    intro P
    constructor
    · intro hP
      obtain ⟨w', hw', rfl⟩ := Finset.mem_image.1 hP
      have hw'' : 0 < w'.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0) :=
        hfin.mem_toFinset.1 hw'
      rwa [← toC_jq K q N hqN, ord_toC] at hw''
    · intro hP
      obtain ⟨w', rfl⟩ := restrictAlong_toC_surjective K q N hqN P
      refine Finset.mem_image.2 ⟨w', hfin.mem_toFinset.2 ?_, rfl⟩
      show 0 < w'.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0)
      rwa [← toC_jq K q N hqN, ord_toC]

  obtain ⟨f, -, hSf, -, -, hB1, -⟩ :=
    exists_orbitMap_cyclicAddSubgroup_places_evalAt_jqNModC_eq_and_ord_sub_eq_natCard K N hNK 0
      (WeierstrassCurve.ofJ 0) (WeierstrassCurve.ofJ_j 0) S hS

  have hmem : ρ w ∈ S := (hS _).2 (by rwa [← toC_jq K q N hqN, ord_toC] at hposj)
  obtain ⟨H, hH⟩ := hSf _ hmem
  obtain ⟨Q, hHQ, hQN⟩ := exists_generator H.1 H.2
  have hΔ := WeierstrassCurve.fullKernelQuotient_discriminant_ne_zero N (WeierstrassCurve.ofJ (0 : K))
    hNK Q hQN

  have hval := hB1 H Q hHQ hQN hΔ
  rw [fullKernelQuotient_j_eq_zero_of_j_eq_zero_of_ringChar hchar (WeierstrassCurve.ofJ 0)
    (WeierstrassCurve.ofJ_j 0) Q hQN hΔ, hH] at hval

  have hreg : ((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N))
      ∈ (ρ w).toValuationSubring := by
    refine (ρ w).mem_of_ord_nonneg ?_ ?_
    · exact fun h => jqNModC_ne_zero (K := K) N (congrArg Subtype.val h)
    · have h := hcw.jNGeomGen_mem
      have h' := w.ord_nonneg_of_mem h
      have : w.ord (jNGeomGen K N) = (ρ w).ord
          ((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N)) := by
        rw [← ord_toC K q N hqN]
        rfl
      rw [← this]
      exact h'
  have hposN : 0 < (ρ w).ord (((⟨jqNModC K N, jqModCd_mem_full K N (dvd_refl N)⟩ : modularFunctionFieldFullC K N))
      - algebraMap K (modularFunctionFieldFullC K N) 0) := by
    have h := ord_sub_evalAt_pos (isRational_full (ρ w)) hreg ?_
    · rw [hval] at h
      exact h
    · rw [hval]
      exact fun h => jqNModC_ne_zero (K := K) N (by simpa using congrArg Subtype.val h)

  have hposN' : 0 < w.ord (jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) 0) := by
    rw [← toC_jqN K q N hqN, ord_toC]
    exact hposN
  have hc : IsCentreOf K N (w.evalAt (jGeomGen K N), 0) w := ⟨hcw1, hposN'⟩
  exact hc.evalAt_jNGeomGen

end SecondValueVanishing

open AlgebraicCurve ModularCurve SecondValueVanishing in
theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {K : Type*} [Field K] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hqlt5 : q < 5) (hqN : ¬ q ∣ N)
    {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K) :
    w.evalAt (jNGeomGen K N) = 0 := by
  have hq : q.Prime := Fact.out
  have hjss : w.evalAt (jGeomGen K N) ∈ ssJSet q K := (show IsSupersingularPlace q N K w from hw).2.2
  have hpow := pow_q_sq_eq_self_of_mem_ssJSet q hjss
  have h2 := hq.two_le
  have h4 : q ≠ 4 := fun h => by subst h; exact absurd hq (by decide)
  obtain rfl | rfl : q = 2 ∨ q = 3 := by omega
  · exact evalAt_jNGeomGen_eq_zero hqN (Or.inl (ringChar.eq K 2)) hw
      (eq_zero_of_mem_ssJSet_two _ hjss hpow)
  · exact evalAt_jNGeomGen_eq_zero hqN (Or.inr (ringChar.eq K 3)) hw
      (eq_zero_of_mem_ssJSet_three _ hjss hpow)

#print axioms solution

end S_ModularCurve_evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five
end P2MW
export P2MW.S_ModularCurve_evalAt_jNGeomGen_eq_zero_of_mem_ssPlaces_of_lt_five (solution)
