-- Prove2me | solution 1 for ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/090de4c0-8ca2-5e6a-bde4-444f6e3bb4bf

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace SupersingularPlacesOverEllipticCentre

private theorem jNGeomGen_mem_of_jGeomGen_mem (K : Type*) [Field K] (N : ℕ) [NeZero N]
    {w : Place K (modularFunctionFieldC K N)} (hj : jGeomGen K N ∈ w.toValuationSubring) :
    jNGeomGen K N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  have hfac : Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N)) (jGeomGen K N)
      = (SubringClass.subtype w.toValuationSubring).comp
          (Polynomial.eval₂RingHom (Int.castRingHom w.toValuationSubring) ⟨jGeomGen K N, hj⟩) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp
  refine w.mem_of_eval_monic_eq_zero
    (P := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N))
      (jGeomGen K N)))
    (data.monic.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map, hfac, RingHom.comp_apply]
    exact SetLike.coe_mem _
  · rw [Polynomial.eval_map]
    exact evalModularPair_jGeomGen_eq_zero K N data

private theorem mem_ssPlaces_and_evalAt_eq_iff_ord_pos (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [DecidableEq K] [IsAlgClosed K] {a : K} (ha : a ∈ ssJSet q K)
    (w : Place K (modularFunctionFieldC K N)) :
    (w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a)
      ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  constructor
  · rintro ⟨hss, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at hss
    have hc : 0 < w.ord (jGeomGen K N
        - algebraMap K (modularFunctionFieldC K N) (w.evalAt (jGeomGen K N))) :=
      (exists_isCentreOf_of_isRational hss.1 hss.2.1).1
    rwa [hev] at hc
  · intro hpos
    have hrat : w.IsRational :=
      (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed K N w)
    have hj : jGeomGen K N ∈ w.toValuationSubring := by
      have h := add_mem (w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N a) hpos.le)
        (w.algebraMap_mem' a)
      rwa [sub_add_cancel] at h
    have hjN : jNGeomGen K N ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem K N hj
    have hev : w.evalAt (jGeomGen K N) = a := by
      rw [w.evalAt_congr hj (w.algebraMap_mem' a) (Or.inr hpos), w.evalAt_algebraMap]
    refine ⟨?_, hev⟩
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff]
    refine ⟨hrat, ⟨hj, hjN⟩, ?_⟩
    rw [hev]
    exact ha

private theorem exists_model (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [CharP K q]
    (a : K) (ha : a = 0 ∨ a = 1728) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic), E₀.j = a ∧ E₀.map (frobenius K q) = E₀ := by
  have hq := (Fact.out : q.Prime)
  have hunit : ∀ n : ℕ, ¬ q ∣ n → IsUnit (n : K) := fun n hn =>
    isUnit_iff_ne_zero.mpr (fun h => hn ((CharP.cast_eq_zero_iff K q n).mp h))
  have h1728 : (1728 : K) = ((1728 : ℕ) : K) := by norm_num
  by_cases hq2 : q = 2
  · subst hq2
    haveI : Fact (IsUnit (3 : K)) := ⟨by simpa using hunit 3 (by decide)⟩
    refine ⟨WeierstrassCurve.ofJ0 K, inferInstance, ?_, ?_⟩
    · rw [WeierstrassCurve.ofJ0_j]
      have h0 : (1728 : K) = 0 := by
        rw [h1728]; exact (CharP.cast_eq_zero_iff K 2 1728).mpr (by decide)
      rcases ha with rfl | rfl
      · rfl
      · exact h0.symm
    · simp [WeierstrassCurve.ofJ0, WeierstrassCurve.map]
  by_cases hq3 : q = 3
  · subst hq3
    haveI : Fact (IsUnit (2 : K)) := ⟨by simpa using hunit 2 (by decide)⟩
    refine ⟨WeierstrassCurve.ofJ1728 K, inferInstance, ?_, ?_⟩
    · rw [WeierstrassCurve.ofJ1728_j]
      have h0 : (1728 : K) = 0 := by
        rw [h1728]; exact (CharP.cast_eq_zero_iff K 3 1728).mpr (by decide)
      rcases ha with rfl | rfl
      · exact h0
      · rfl
    · simp [WeierstrassCurve.ofJ1728, WeierstrassCurve.map]
  have hnd2 : ¬ q ∣ 2 := fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  have hnd3 : ¬ q ∣ 3 := fun h => hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h)
  rcases ha with rfl | rfl
  · haveI : Fact (IsUnit (3 : K)) := ⟨by simpa using hunit 3 hnd3⟩
    exact ⟨WeierstrassCurve.ofJ0 K, inferInstance, WeierstrassCurve.ofJ0_j K,
      by simp [WeierstrassCurve.ofJ0, WeierstrassCurve.map]⟩
  · haveI : Fact (IsUnit (2 : K)) := ⟨by simpa using hunit 2 hnd2⟩
    exact ⟨WeierstrassCurve.ofJ1728 K, inferInstance, WeierstrassCurve.ofJ1728_j K,
      by simp [WeierstrassCurve.ofJ1728, WeierstrassCurve.map]⟩

end SupersingularPlacesOverEllipticCentre

open SupersingularPlacesOverEllipticCentre in
theorem solution
    (q N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (K : Type*) [Field K] [DecidableEq K]
    [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (a : K) (ha : a = 0 ∨ a = 1728) (hss : a ∈ ModularCurve.ssJSet q K) :
    ∃ e : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K ∧ w.evalAt (ModularCurve.jGeomGen K N) = a} ≃
          {x : ModularCurve.ModuliPoint N K // x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a},
      ∀ (w w' : {w : Place K (ModularCurve.modularFunctionFieldC K N) //
            w ∈ ModularCurve.ssPlaces q N K ∧ w.evalAt (ModularCurve.jGeomGen K N) = a}),
        ModularCurve.arithFrobC q K N • (w : Place K (ModularCurve.modularFunctionFieldC K N))
            = (w' : Place K (ModularCurve.modularFunctionFieldC K N)) →
          ((e w' : {x : ModularCurve.ModuliPoint N K //
              x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a}) : ModularCurve.ModuliPoint N K)
            = ModularCurve.ModuliPoint.map (frobenius K q)
                ((e w : {x : ModularCurve.ModuliPoint N K //
                    x ∈ ModularCurve.ssLocus q N K ∧ ModularCurve.ModuliPoint.j x = a}) : ModularCurve.ModuliPoint N K) := by
  obtain ⟨E₀, hE, hj, hfr⟩ := exists_model q K a ha
  haveI := hE
  subst hj
  obtain ⟨f, g, h1, h2, h3, h4, h5, h6, h7⟩ :=
    ModularCurve.exists_orbitMap_places_moduliPoint_arithFrobC_compat_univ q N hqN K E₀ hfr
  have hbr := fun w : Place K (modularFunctionFieldC K N) =>
    mem_ssPlaces_and_evalAt_eq_iff_ord_pos q N K hss w
  choose F hF using h2
  choose G hG using h6
  let e : {w : Place K (modularFunctionFieldC K N) //
            w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = E₀.j} ≃
          {x : ModuliPoint N K // x ∈ ssLocus q N K ∧ ModuliPoint.j x = E₀.j} :=
    { toFun := fun w => ⟨g (F w.1 ((hbr w.1).mp w.2)),
        mem_ssLocus_iff.mpr (by rw [h5]; exact hss), h5 _⟩
      invFun := fun x => ⟨f (G x.1 x.2.2), (hbr _).mpr (h1 _)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        show f (G _ _) = w.1
        rw [← hF w.1 ((hbr w.1).mp w.2)]
        exact (h4 _ _).mp (hG _ _)
      right_inv := by
        intro x
        apply Subtype.ext
        show g (F _ _) = x.1
        rw [← hG x.1 x.2.2]
        exact (h4 _ _).mpr (hF _ _) }
  refine ⟨e, ?_⟩
  intro w w' hww'
  obtain ⟨H'', hf'', hg''⟩ := h7 (F w.1 ((hbr w.1).mp w.2))
  show g (F w'.1 _) = ModuliPoint.map (frobenius K q) (g (F w.1 _))
  rw [← hg'']
  apply (h4 _ _).mpr
  rw [hF, hf'', hF]
  exact hww'.symm

end S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ
end P2MW
export P2MW.S_ModularCurve_exists_equiv_ssPlaces_ssLocus_fibre_of_elliptic_centre_univ (solution)
