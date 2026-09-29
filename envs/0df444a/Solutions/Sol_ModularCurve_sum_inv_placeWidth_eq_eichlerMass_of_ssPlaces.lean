-- Prove2me | solution 1 for ModularCurve.sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/4ceef085-ae99-51d8-907f-96ad165f8d15

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_EichlerMass

import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_sum_inv_jWidth_eq_of_ssJSet
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve Polynomial

noncomputable section

namespace HwCurve

variable {K : Type*} [Field K] {N : ℕ} [NeZero N]

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K (modularFunctionFieldC K N)) :
    w.IsRational :=
  (Place.isRational_iff_deg_eq_one w).mpr (place_deg_eq_one_of_isAlgClosed K N w)

theorem jNGeomGen_mem_of_jGeomGen_mem (w : Place K (modularFunctionFieldC K N))
    (hJ : jGeomGen K N ∈ w.toValuationSubring) : jNGeomGen K N ∈ w.toValuationSubring := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  set O := w.toValuationSubring

  let c : Polynomial ℤ →+* O := Polynomial.eval₂RingHom (Int.castRingHom O) ⟨jGeomGen K N, hJ⟩
  have hmonic : (data.Φ.map c).Monic := data.monic.map c
  have hroot : Polynomial.eval₂ (algebraMap O (modularFunctionFieldC K N)) (jNGeomGen K N)
      (data.Φ.map c) = 0 := by
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap O (modularFunctionFieldC K N)).comp c =
        Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC K N)) (jGeomGen K N) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp [c]
    rw [hcomp]
    exact evalModularPair_jGeomGen_eq_zero K N data
  have hint : IsIntegral O (jNGeomGen K N) := ⟨data.Φ.map c, hmonic, hroot⟩
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := O) (K := modularFunctionFieldC K N)).mp hint
  rw [← hy]
  exact y.2

theorem jGeomGen_mem_of_ord_pos (w : Place K (modularFunctionFieldC K N)) (a : K)
    (h : 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a)) :
    jGeomGen K N ∈ w.toValuationSubring := by
  have hmem : jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero K N a) h.le
  have := add_mem hmem (w.algebraMap_mem' a)
  rwa [sub_add_cancel] at this

section Fibre

variable {q : ℕ}

theorem mem_fibre_iff [IsAlgClosed K] [DecidableEq K] {a : K} (ha : a ∈ ssJSet q K)
    (w : Place K (modularFunctionFieldC K N)) :
    0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) ↔
      w ∈ ssPlaces q N K ∧ w.evalAt (jGeomGen K N) = a := by
  constructor
  · intro h
    have hrat : w.IsRational := isRational_of_isAlgClosed w
    have hJ : jGeomGen K N ∈ w.toValuationSubring := jGeomGen_mem_of_ord_pos w a h
    have hJN : jNGeomGen K N ∈ w.toValuationSubring := jNGeomGen_mem_of_jGeomGen_mem w hJ

    have hcentre : IsCentreOf K N (a, w.evalAt (jNGeomGen K N)) w :=
      ⟨h, ord_sub_evalAt_pos_of_isRational hrat hJN (jNGeomGen_sub_algebraMap_ne_zero K N _)⟩
    have hev : w.evalAt (jGeomGen K N) = a := hcentre.evalAt_jGeomGen
    refine ⟨⟨hrat, ⟨hJ, hJN⟩, ?_⟩, hev⟩
    rw [hev]
    exact ha
  · rintro ⟨hw, hev⟩
    have hc := (IsSupersingularPlace.isCentreOf_evalAt hw).1
    rw [hev] at hc
    exact hc

theorem placeRamificationJ_eq_ord [DecidableEq K] {w : Place K (modularFunctionFieldC K N)}
    (hw : w ∈ ssPlaces q N K) {a : K} (hev : w.evalAt (jGeomGen K N) = a) :
    (placeRamificationJ N w : ℤ) = w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
  have hc := (IsSupersingularPlace.isCentreOf_evalAt hw).1
  unfold placeRamificationJ
  rw [hev] at hc ⊢
  exact Int.toNat_of_nonneg hc.le

end Fibre

theorem inv_placeWidth_eq {q : ℕ} [Fact q.Prime] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N) {w : Place K (modularFunctionFieldC K N)} (hw : w ∈ ssPlaces q N K)
    {a : K} (hev : w.evalAt (jGeomGen K N) = a) :
    ((placeWidth N w : ℚ))⁻¹ =
      (w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) : ℚ) / (jWidth a : ℚ) := by
  have hdvd : placeRamificationJ N w ∣ jWidth (w.evalAt (jGeomGen K N)) :=
    placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq5 hqN hw
  rw [hev] at hdvd
  have hpr : (placeRamificationJ N w : ℤ) = w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) :=
    placeRamificationJ_eq_ord hw hev
  have hprpos : 0 < placeRamificationJ N w := by
    have hc := (IsSupersingularPlace.isCentreOf_evalAt hw).1
    rw [hev] at hc
    have : (0 : ℤ) < (placeRamificationJ N w : ℤ) := by rw [hpr]; exact hc
    exact_mod_cast this
  have hjw : 0 < jWidth a := jWidth_pos a

  have hpw : placeWidth N w = jWidth a / placeRamificationJ N w := by
    unfold placeWidth; rw [hev]
  have hcast : (placeWidth N w : ℚ) = (jWidth a : ℚ) / (placeRamificationJ N w : ℚ) := by
    rw [hpw, Nat.cast_div hdvd (by exact_mod_cast hprpos.ne')]
  have hordq : (w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) : ℚ) =
      (placeRamificationJ N w : ℚ) := by
    rw [← hpr]; norm_cast
  rw [hcast, hordq, inv_div]

theorem sum_filter_inv_placeWidth_eq {q : ℕ} [Fact q.Prime] [CharP K q] [IsAlgClosed K] [DecidableEq K]
    (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N) (W : Finset (Place K (modularFunctionFieldC K N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N K) {a : K} (ha : a ∈ ssJSet q K) :
    (∑ w ∈ W with w.evalAt (jGeomGen K N) = a, ((placeWidth N w : ℚ))⁻¹) =
        (dedekindPsi N : ℚ) / (jWidth a : ℚ) ∧
      ∃ w ∈ W, w.evalAt (jGeomGen K N) = a := by
  classical
  have hsep := isSeparable_jqNModC_of_good K N q hqN

  set T : Finset (Place K (modularFunctionFieldC K N)) :=
    (finite_setOf_ord_jGeomGen_sub_pos K N hsep a).toFinset with hT_def
  have hT : ∀ w, w ∈ T ↔ 0 < w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) := by
    intro w
    rw [hT_def, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  have hfilter : (W.filter fun w => w.evalAt (jGeomGen K N) = a) = T := by
    ext w
    rw [Finset.mem_filter, hT, mem_fibre_iff ha, hW]

  have hsum : ∑ w ∈ T, w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) = dedekindPsi N :=
    sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN K hsep a T hT
  refine ⟨?_, ?_⟩
  · rw [hfilter]
    have hterm : ∀ w ∈ T, ((placeWidth N w : ℚ))⁻¹ =
        (w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) a) : ℚ) / (jWidth a : ℚ) := by
      intro w hwT
      obtain ⟨hw, hev⟩ := (mem_fibre_iff ha w).mp ((hT w).mp hwT)
      exact inv_placeWidth_eq hq5 hqN hw hev
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    congr 1
    have := congrArg (fun z : ℤ => (z : ℚ)) hsum
    push_cast at this
    exact this
  ·
    have hpos : 0 < dedekindPsi N := dedekindPsi_pos N (NeZero.ne N)
    have hne : T.Nonempty := by
      by_contra hT0
      rw [Finset.not_nonempty_iff_eq_empty] at hT0
      rw [hT0, Finset.sum_empty] at hsum
      have : (dedekindPsi N : ℤ) = 0 := hsum.symm
      omega
    obtain ⟨w, hwT⟩ := hne
    have hwf : w ∈ W.filter fun w => w.evalAt (jGeomGen K N) = a := by rw [hfilter]; exact hwT
    rw [Finset.mem_filter] at hwf
    exact ⟨w, hwf.1, hwf.2⟩

end HwCurve

end

open HwCurve in

theorem solution
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hq5 : 5 ≤ q) (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) :
    ∑ w ∈ W, ((placeWidth N w : ℚ))⁻¹ = eichlerMass N q := by
  classical

  set S : Finset k := W.image fun w => w.evalAt (jGeomGen k N) with hS_def
  have hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q k := by
    intro j
    constructor
    · intro hj
      obtain ⟨w, hwW, rfl⟩ := Finset.mem_image.mp hj
      exact ((hW w).mp hwW).2.2
    · intro hj
      obtain ⟨w, hwW, hev⟩ := (sum_filter_inv_placeWidth_eq hq5 hqN W hW hj).2
      exact Finset.mem_image.mpr ⟨w, hwW, hev⟩
  have hmaps : ∀ w ∈ W, (fun w => w.evalAt (jGeomGen k N)) w ∈ S :=
    fun w hw => Finset.mem_image_of_mem _ hw

  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ a ∈ S, (∑ w ∈ W with w.evalAt (jGeomGen k N) = a, ((placeWidth N w : ℚ))⁻¹) =
      (dedekindPsi N : ℚ) * ((jWidth a : ℚ))⁻¹ := by
    intro a haS
    rw [(sum_filter_inv_placeWidth_eq hq5 hqN W hW ((hS a).mp haS)).1, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum, sum_inv_jWidth_eq_of_ssJSet q hq5 k S hS]
  unfold eichlerMass
  ring

end S_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces
end P2MW
export P2MW.S_ModularCurve_sum_inv_placeWidth_eq_eichlerMass_of_ssPlaces (solution)
