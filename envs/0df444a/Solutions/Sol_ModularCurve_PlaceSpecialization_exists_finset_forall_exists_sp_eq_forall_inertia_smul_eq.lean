-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/07cc11f7-052a-59a7-97b6-c0ae0463865e

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_exists_finset_place_eq_of_ord_jqModC_sub_pos
import Theorems.Thm_ModularCurve_modularFunctionFieldBar_eq_modularFunctionFieldC
import Theorems.Thm_ModularCurve_CharPModel_place_eq_of_ord_pos_of_derivative_evalEval_ne_zero
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_Polynomial_exists_root_reducing_to_simple_root
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal
import Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_finrank
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply"
p2m_attr_erase "simp" "HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq.ModularCurve Polynomial IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence jGeomGen jNGeomGen transcendental_jqNModC jGeomGen_sub_algebraMap_ne_zero jNGeomGen_sub_algebraMap_ne_zero evalModularPair map_evalModularPair evalModularPair_jq_eq_zero IsCentreOf exists_isCentreOf_of_isRational transcendental_jqModC exists_finset_place_eq_of_ord_jqModC_sub_pos modularFunctionFieldBar_eq_modularFunctionFieldC CharPModel.place_eq_of_ord_pos_of_derivative_evalEval_ne_zero finite_setOf_ord_jGeomGen_sub_pos isSeparable_jqNModC_of_natCast_ne_zero relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi isCurveOver_modularFunctionFieldC_of_perfectField ord_jBar_sub_eq_one_of_ne_zero_of_ne jBar sum_ord_jBar_sub_eq_finrank CompEq.finrank_adjoin_jBar_eq_dedekindPsi forall_ord_jBar_sub_le_zero_or_exists_ord_pos arithmeticGalois_smul_coeffEmb minpoly_jqNModC_eq nonempty_modularPolynomialData coeffEmb_jq coeffEmb_jqN"
namespace UnramifiedLift
p2m_open "ModularCurve~dedekindPsi_pos"

local notation "L" => AlgebraicClosure ℚ

section Notation
variable (N : ℕ) [NeZero N]

abbrev jB : modularFunctionFieldBar N :=
  ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (modularFunctionField_le_full N (jq_mem N))⟩

abbrev jNB : modularFunctionFieldBar N :=
  ⟨coeffEmb L (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩

theorem coe_jB : ((jB N : modularFunctionFieldBar N) : LaurentSeries L) = jqModC L := coeffEmb_jq L
theorem coe_jNB : ((jNB N : modularFunctionFieldBar N) : LaurentSeries L) = jqNModC L N := coeffEmb_jqN L N

theorem jB_eq_jBar : (jB N : modularFunctionFieldBar N) = jBar N := rfl

theorem jB_sub_algebraMap_ne_zero (a : L) : (jB N : modularFunctionFieldBar N) - algebraMap L _ a ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hcoe : jqModC L = algebraMap L (LaurentSeries L) a := by
    have := congrArg (fun z : modularFunctionFieldBar N => (z : LaurentSeries L)) h
    simpa [coeffEmb_jq] using this
  exact transcendental_jqModC L (hcoe ▸ isAlgebraic_algebraMap a)

theorem jNB_sub_algebraMap_ne_zero (b : L) : (jNB N : modularFunctionFieldBar N) - algebraMap L _ b ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hcoe : jqNModC L N = algebraMap L (LaurentSeries L) b := by
    have := congrArg (fun z : modularFunctionFieldBar N => (z : LaurentSeries L)) h
    have e : coeffEmb L (qExpand ℚ N jq) = jqNModC L N := coeffEmb_jqN L N
    simpa [e] using this
  exact transcendental_jqNModC L N (hcoe ▸ isAlgebraic_algebraMap b)

end Notation

section Poly
variable {R S : Type*} [CommRing R] [CommRing S]

abbrev phiAt (Φ : Polynomial (Polynomial ℤ)) (x : R) : Polynomial R :=
  Φ.map (eval₂RingHom (Int.castRingHom R) x)

theorem eval_phiAt (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    (phiAt Φ x).eval y = evalModularPair x y Φ := by
  rw [eval_map]
  rfl

theorem comp_eval₂RingHom_int (f : R →+* S) (x : R) :
    f.comp (eval₂RingHom (Int.castRingHom R) x) = eval₂RingHom (Int.castRingHom S) (f x) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem phiAt_map (f : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (x : R) :
    (phiAt Φ x).map f = phiAt Φ (f x) := by
  rw [Polynomial.map_map, comp_eval₂RingHom_int]

theorem phiAt_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : R) : (phiAt Φ x).Monic := hΦ.map _

theorem evalEval_map_mapRingHom (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    (Φ.map (mapRingHom (Int.castRingHom R))).evalEval x y = evalModularPair x y Φ := by
  unfold Polynomial.evalEval evalModularPair
  rw [eval_map, ← coe_evalRingHom, hom_eval₂, coe_evalRingHom, eval_C]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom, Polynomial.map_X,
    Polynomial.eval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem derivative_phiAt (Φ : Polynomial (Polynomial ℤ)) (x : R) :
    derivative (phiAt Φ x) = phiAt (derivative Φ) x := derivative_map _ _

end Poly

section GenericPlace
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_ord_ne_zero [h : HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    {v : Place K F | v.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := h.exists_divisor f hf
  refine (D.support.finite_toSet).subset ?_
  intro v hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD v]
  exact hv

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).surjective

theorem ord_sub_evalAt_pos (v : Place K F) (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f) = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

theorem residue_eq_algebraMap_of_ord_sub_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (c : K)
    (h : 0 < v.ord (f - algebraMap K F c)) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField c := by
  have hmem : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' c)
  have hmax := v.mk_mem_maximalIdeal_of_ord_pos hmem h
  have hcoe : (⟨f - algebraMap K F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - algebraMap K v.toValuationSubring c := by
    refine Subtype.ext ?_
    show f - algebraMap K F c = f - (algebraMap K v.toValuationSubring c : F)
    rw [Place.coe_algebraMap]
  rw [hcoe, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hmax
  rw [hmax, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

theorem evalAt_eq_of_ord_sub_pos (v : Place K F) (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (c : K) (h : 0 < v.ord (f - algebraMap K F c)) : v.evalAt f = c := by
  apply (algebraMap K v.ResidueField).injective
  rw [v.algebraMap_evalAt hrat hf, residue_eq_algebraMap_of_ord_sub_pos v hf c h]

theorem residue_ne_zero_of_ord_eq_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (h : v.ord f = 0) : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
  have h1 : v.adicValuation f = 1 := (v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
  exact (hu.map (IsLocalRing.residue v.toValuationSubring)).ne_zero

theorem mem_of_ord_pos (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 < v.ord f) : f ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg hf h.le

theorem mem_of_ord_sub_algebraMap_pos (v : Place K F) {f : F} (c : K) (hne : f - algebraMap K F c ≠ 0)
    (h : 0 < v.ord (f - algebraMap K F c)) : f ∈ v.toValuationSubring := by
  have := add_mem (v.mem_of_ord_nonneg hne h.le) (v.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

end GenericPlace

section Residue
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residue_evalModularPair (w : Place K F) {x y : F}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring) {a b : K}
    (hxa : residue w.toValuationSubring ⟨x, hx⟩ = algebraMap K w.ResidueField a)
    (hyb : residue w.toValuationSubring ⟨y, hy⟩ = algebraMap K w.ResidueField b) (Ψ : Polynomial (Polynomial ℤ)) :
    ∃ hmem : evalModularPair x y Ψ ∈ w.toValuationSubring,
      residue w.toValuationSubring ⟨evalModularPair x y Ψ, hmem⟩
        = algebraMap K w.ResidueField (evalModularPair a b Ψ) := by
  have hcoe : ((evalModularPair (⟨x, hx⟩ : w.toValuationSubring) ⟨y, hy⟩ Ψ : w.toValuationSubring) : F)
      = evalModularPair x y Ψ :=
    map_evalModularPair (SubringClass.subtype w.toValuationSubring) _ _ Ψ
  refine ⟨hcoe ▸ (evalModularPair (⟨x, hx⟩ : w.toValuationSubring) ⟨y, hy⟩ Ψ).2, ?_⟩
  have heq : (⟨evalModularPair x y Ψ, hcoe ▸ (evalModularPair (⟨x, hx⟩ : w.toValuationSubring) ⟨y, hy⟩ Ψ).2⟩
      : w.toValuationSubring) = evalModularPair (⟨x, hx⟩ : w.toValuationSubring) ⟨y, hy⟩ Ψ :=
    Subtype.ext hcoe.symm
  rw [heq, map_evalModularPair, hxa, hyb, ← map_evalModularPair]

theorem evalModularPair_eq_zero_of_residue (w : Place K F) {x y : F}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring) {a b : K}
    (hxa : residue w.toValuationSubring ⟨x, hx⟩ = algebraMap K w.ResidueField a)
    (hyb : residue w.toValuationSubring ⟨y, hy⟩ = algebraMap K w.ResidueField b) (Ψ : Polynomial (Polynomial ℤ))
    (h0 : evalModularPair x y Ψ = 0) : evalModularPair a b Ψ = 0 := by
  obtain ⟨hmem, hres⟩ := residue_evalModularPair w hx hy hxa hyb Ψ
  have : residue w.toValuationSubring ⟨evalModularPair x y Ψ, hmem⟩ = 0 := by
    rw [show (⟨evalModularPair x y Ψ, hmem⟩ : w.toValuationSubring) = 0 from Subtype.ext h0, map_zero]
  rw [hres] at this
  exact (map_eq_zero_iff _ (algebraMap K w.ResidueField).injective).mp this

theorem evalModularPair_ne_zero_of_ord_eq_zero (w : Place K F) {x y : F}
    (hx : x ∈ w.toValuationSubring) (hy : y ∈ w.toValuationSubring) {a b : K}
    (hxa : residue w.toValuationSubring ⟨x, hx⟩ = algebraMap K w.ResidueField a)
    (hyb : residue w.toValuationSubring ⟨y, hy⟩ = algebraMap K w.ResidueField b) (Ψ : Polynomial (Polynomial ℤ))
    (hne : evalModularPair x y Ψ ≠ 0) (hord : w.ord (evalModularPair x y Ψ) = 0) : evalModularPair a b Ψ ≠ 0 := by
  obtain ⟨hmem, hres⟩ := residue_evalModularPair w hx hy hxa hyb Ψ
  intro h
  have := residue_ne_zero_of_ord_eq_zero w hmem hne hord
  rw [hres, h, map_zero] at this
  exact this rfl

end Residue

section Lifts
variable {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem red_eq_zero_of_mem_maximalIdeal (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) {x : A}
    (hx : x ∈ maximalIdeal A) : red x = 0 :=
  ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal A q red hx

theorem liesOverPrime_of_red (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hq : red ((q : ℕ) : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hnu : ¬ IsUnit ((q : ℕ) : A) := by
    intro hu
    have := hu.map red
    rw [hq] at this
    exact not_isUnit_zero this
  show ((q : ℕ) : L) ∈ A.nonunits
  have hcoe : ((q : ℕ) : L) = (((q : ℕ) : A) : L) := by push_cast; rfl
  rw [hcoe, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hnu

theorem exists_root_lift (red : A →+* k) (f : Polynomial A) (hf : f.Monic) (bt : k)
    (hroot : (f.map red).IsRoot bt) (hsimple : ¬ (derivative (f.map red)).IsRoot bt) :
    ∃ b : A, f.IsRoot b ∧ red b = bt ∧ ∀ b' : A, f.IsRoot b' → red b' = bt → b' = b := by
  classical
  set fL : Polynomial L := f.map (algebraMap A L) with hfL
  have hfLm : fL.Monic := hf.map _
  have hcard : fL.roots.card = fL.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits fL)

  have hmemA : ∀ r ∈ fL.roots, r ∈ A := by
    intro r hr
    have hint : IsIntegral A r := ⟨f, hf, by
      rw [← eval_map]
      exact (mem_roots hfLm.ne_zero).mp hr⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint
    rw [← hy]
    exact y.2
  let s : Multiset A := fL.roots.attach.map (fun r => (⟨r.1, hmemA r.1 r.2⟩ : A))
  have hs_map : s.map (algebraMap A L) = fL.roots := by
    rw [Multiset.map_map]
    exact Multiset.attach_map_val fL.roots
  have hprod : f = (s.map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.map_injective (algebraMap A L) Subtype.val_injective
    rw [Polynomial.map_multiset_prod, Multiset.map_map,
      show (Polynomial.map (algebraMap A L) ∘ fun a : A => Polynomial.X - Polynomial.C a) = (fun r : L => Polynomial.X - Polynomial.C r) ∘ (algebraMap A L)
        from funext fun a => by simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C],
      ← Multiset.map_map, hs_map]
    exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hfLm hcard).symm

  have hfk0 : f.map red ≠ 0 := (hf.map red).ne_zero
  have hmult : ((s.map fun a => Polynomial.X - Polynomial.C a).prod.map red).rootMultiplicity bt = 1 := by
    rw [← hprod]
    have h1 : 0 < (f.map red).rootMultiplicity bt := (rootMultiplicity_pos hfk0).mpr hroot
    have h2 : ¬ 1 < (f.map red).rootMultiplicity bt := fun h =>
      hsimple ((one_lt_rootMultiplicity_iff_isRoot hfk0).mp h).2
    omega
  obtain ⟨b, hbs, hbred, -, huniq⟩ := Polynomial.exists_root_reducing_to_simple_root red s bt hmult
  have hroots : ∀ b' : A, f.IsRoot b' ↔ b' ∈ s := by
    intro b'
    rw [hprod, IsRoot.def, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map]
    constructor
    · rintro ⟨a, ha, h0⟩
      have h0' : b' = a := by
        simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h0
        exact h0
      exact h0' ▸ ha
    · intro h
      exact ⟨b', h, by simp⟩
  exact ⟨b, (hroots b).mpr hbs, hbred, fun b' hb' hred' => huniq b' ((hroots b').mp hb') hred'⟩

theorem exists_pow_red_eq_one (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) (a₀ : A) (h0 : red a₀ ≠ 0) :
    ∃ m : ℕ, ¬ q ∣ m ∧ (red a₀) ^ m = 1 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  letI : Algebra (ZMod q) k := ZMod.algebra k q

  have hQ : IsAlgebraic ℚ (a₀ : L) := Algebra.IsAlgebraic.isAlgebraic _
  have hZ : IsAlgebraic ℤ (a₀ : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr hQ
  obtain ⟨p, hp0, hp⟩ := hZ
  set p₁ := p.primPart with hp₁
  have hp₁0 : aeval (a₀ : L) p₁ = 0 := by
    have h := hp
    rw [p.eq_C_content_mul_primPart, map_mul, aeval_C, mul_eq_zero] at h
    refine h.resolve_left ?_
    rw [eq_intCast, Int.cast_eq_zero, content_eq_zero_iff]
    exact hp0
  have hprim : p₁.IsPrimitive := isPrimitive_primPart p

  have hred_ne : p₁.map (Int.castRingHom (ZMod q)) ≠ 0 := by
    intro h
    have hdvd : Polynomial.C (q : ℤ) ∣ p₁ := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : ((p₁.coeff i : ℤ) : ZMod q) = 0 := by
        rw [← eq_intCast (Int.castRingHom (ZMod q)), ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hi
    have hu : IsUnit (q : ℤ) := (isPrimitive_iff_isUnit_of_C_dvd.mp hprim) _ hdvd
    have hq1 : (q : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
    exact (Fact.out : q.Prime).one_lt.ne' (by simpa using hq1)

  have h1 : aeval a₀ p₁ = 0 := by
    apply Subtype.val_injective
    show (algebraMap A L) (p₁.eval₂ (algebraMap ℤ A) a₀) = ((0 : A) : L)
    rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero, ← hp₁0, aeval_def]
    congr 1 <;> first | rfl | exact Subsingleton.elim _ _
  have haeval : aeval (red a₀) (p₁.map (Int.castRingHom (ZMod q))) = 0 := by
    rw [aeval_def, eval₂_map,
      show (algebraMap (ZMod q) k).comp (Int.castRingHom (ZMod q)) = red.comp (algebraMap ℤ A) from
        RingHom.ext_int _ _,
      ← hom_eval₂, ← aeval_def, h1, map_zero]
  have halg : IsAlgebraic (ZMod q) (red a₀) := ⟨_, hred_ne, haeval⟩
  have hint : IsIntegral (ZMod q) (red a₀) := isAlgebraic_iff_isIntegral.mp halg

  let E := IntermediateField.adjoin (ZMod q) ({red a₀} : Set k)
  haveI : FiniteDimensional (ZMod q) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod q)
  letI : Fintype E := Fintype.ofFinite E
  set x : E := ⟨red a₀, IntermediateField.mem_adjoin_simple_self (ZMod q) (red a₀)⟩ with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply h0
    simpa [hx] using congrArg (fun z : E => (z : k)) h
  refine ⟨Fintype.card E - 1, ?_, ?_⟩
  ·
    have hcard : Fintype.card E = q ^ Module.finrank (ZMod q) E := by
      rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
    have hn : 0 < Module.finrank (ZMod q) E := Module.finrank_pos
    intro hdvd
    have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
    have hpow : q ∣ q ^ Module.finrank (ZMod q) E := dvd_pow_self q hn.ne'
    have hle : 1 ≤ q ^ Module.finrank (ZMod q) E := Nat.one_le_pow _ _ (by omega)
    have : q ∣ q ^ Module.finrank (ZMod q) E - (q ^ Module.finrank (ZMod q) E - 1) :=
      Nat.dvd_sub hpow (hcard ▸ hdvd)
    rw [Nat.sub_sub_self hle, Nat.dvd_one] at this
    omega
  · have := FiniteField.pow_card_sub_one_eq_one x hx0
    have := congrArg (fun z : E => (z : k)) this
    simpa [hx] using this

theorem exists_teichmuller (q : ℕ) [Fact q.Prime] [CharP k q] (red : A →+* k) (a₀ : A) :
    ∃ a : A, red a = red a₀ ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : L) = a := by
  classical
  by_cases h0 : red a₀ = 0
  · exact ⟨0, by rw [map_zero, h0], fun σ _ => by simp⟩
  obtain ⟨m, hqm, hm⟩ := exists_pow_red_eq_one q red a₀ h0
  have hm0 : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hmk : (m : k) ≠ 0 := fun h => hqm ((CharP.cast_eq_zero_iff k q m).mp h)
  have hmonic : (Polynomial.X ^ m - Polynomial.C (1 : A)).Monic := monic_X_pow_sub_C (1 : A) hm0
  have hmap : (Polynomial.X ^ m - Polynomial.C (1 : A)).map red = Polynomial.X ^ m - Polynomial.C 1 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_one, Polynomial.map_one]
  have hroot : ((Polynomial.X ^ m - Polynomial.C (1 : A)).map red).IsRoot (red a₀) := by
    rw [hmap, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, hm, sub_self]
  have hsimple : ¬ (derivative ((Polynomial.X ^ m - Polynomial.C (1 : A)).map red)).IsRoot (red a₀) := by
    rw [hmap, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero, IsRoot.def,
      eval_mul, eval_C, eval_pow, eval_X]
    exact mul_ne_zero hmk (pow_ne_zero _ h0)
  obtain ⟨ζ, hζroot, hζred, -⟩ :=
    exists_root_lift red (Polynomial.X ^ m - Polynomial.C 1) hmonic (red a₀) hroot hsimple
  refine ⟨ζ, hζred, fun σ hσ => ?_⟩
  have hζm : (ζ : L) ^ m = 1 := by
    have h := hζroot
    rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h
    have := congrArg (fun z : A => (z : L)) h
    simpa using this
  exact ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A (Fact.out : q.Prime)
    (liesOverPrime_of_red q red) hσ hqm hζm

theorem root_mem (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : A) (r : L)
    (hr : evalModularPair (a : L) r Φ = 0) : r ∈ A := by
  have hint : IsIntegral A r := ⟨phiAt Φ a, phiAt_monic hΦ a, by
    rw [← eval_map, phiAt_map, ← hr, eval_phiAt]
    rfl⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hint
  rw [← hy]
  exact y.2

theorem root_smul (Φ : Polynomial (Polynomial ℤ)) (σ : L ≃ₐ[ℚ] L) (a r : L) (ha : σ a = a)
    (hr : evalModularPair a r Φ = 0) : evalModularPair a (σ r) Φ = 0 := by
  have h : (σ : L →+* L) (evalModularPair a r Φ) = evalModularPair ((σ : L →+* L) a) ((σ : L →+* L) r) Φ :=
    map_evalModularPair _ a r Φ
  rw [hr, map_zero, RingHom.coe_coe, ha] at h
  exact h.symm

theorem exists_root_lift_phi (red : A →+* k) (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (a : A) (bt : k)
    (hroot : evalModularPair (red a) bt Φ = 0) (hsimple : evalModularPair (red a) bt (derivative Φ) ≠ 0) :
    ∃ b : A, evalModularPair (a : L) (b : L) Φ = 0 ∧ red b = bt ∧
      ∀ b' : A, evalModularPair (a : L) (b' : L) Φ = 0 → red b' = bt → b' = b := by
  have hcoe : ∀ b' : A, ((evalModularPair a b' Φ : A) : L) = evalModularPair (a : L) (b' : L) Φ :=
    fun b' => map_evalModularPair (algebraMap A L) a b' Φ
  have hconv : ∀ b' : A, evalModularPair (a : L) (b' : L) Φ = 0 ↔ (phiAt Φ a).IsRoot b' := by
    intro b'
    rw [IsRoot.def, eval_phiAt, ← hcoe, ZeroMemClass.coe_eq_zero]
  have hroot' : ((phiAt Φ a).map red).IsRoot bt := by
    rw [phiAt_map, IsRoot.def, eval_phiAt]; exact hroot
  have hsimple' : ¬ (derivative ((phiAt Φ a).map red)).IsRoot bt := by
    rw [phiAt_map, derivative_phiAt, IsRoot.def, eval_phiAt]; exact hsimple
  obtain ⟨b, hb, hbred, huniq⟩ := exists_root_lift red (phiAt Φ a) (phiAt_monic hΦ a) bt hroot' hsimple'
  exact ⟨b, (hconv b).mpr hb, hbred, fun b' hb' h => huniq b' ((hconv b').mp hb') h⟩

end Lifts

section Upstairs
variable (N : ℕ) [NeZero N]

theorem isCurveOver_of_eq {F : IntermediateField L (LaurentSeries L)} (hF : F = modularFunctionFieldC L N) :
    IsCurveOver L F := by
  subst hF
  exact isCurveOver_modularFunctionFieldC_of_perfectField L N

scoped instance isCurveOver_B : IsCurveOver L (modularFunctionFieldBar N) :=
  isCurveOver_of_eq N (modularFunctionFieldBar_eq_modularFunctionFieldC N)

theorem isRational_B (u : Place L (modularFunctionFieldBar N)) : u.IsRational := isRational_of_isCurveOver u

theorem finite_ord_ne_zero_B {f : modularFunctionFieldBar N} (hf : f ≠ 0) :
    {u : Place L (modularFunctionFieldBar N) | u.ord f ≠ 0}.Finite := finite_ord_ne_zero hf

theorem evalModularPair_B_eq_zero (dataN : ModularPolynomialData N) :
    evalModularPair (jB N) (jNB N) dataN.Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldBar N).val.toRingHom (jB N) (jNB N) dataN.Φ
  have hgen : (modularFunctionFieldBar N).val.toRingHom (jB N) = jqModC L := coe_jB N
  have hgenN : (modularFunctionFieldBar N).val.toRingHom (jNB N) = jqNModC L N := coe_jNB N
  rw [hgen, hgenN, evalModularPair_jq_eq_zero L dataN] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldBar N).val.toRingHom.injective).mp hval

theorem place_eq_of_centre_of_eq {F : IntermediateField L (LaurentSeries L)} (hF : F = modularFunctionFieldC L N)
    (dataN : ModularPolynomialData N) (a b : L)
    (hroot : evalModularPair a b dataN.Φ = 0) (hder : evalModularPair a b (derivative dataN.Φ) ≠ 0)
    (x y : F) (hx : (x : LaurentSeries L) = jqModC L) (hy : (y : LaurentSeries L) = jqNModC L N)
    (P Q : Place L F)
    (hPj : 0 < P.ord (x - algebraMap L F a)) (hPjN : 0 < P.ord (y - algebraMap L F b))
    (hQj : 0 < Q.ord (x - algebraMap L F a)) (hQjN : 0 < Q.ord (y - algebraMap L F b)) : P = Q := by
  subst hF
  obtain rfl : x = ⟨jqModC L, jqModC_mem L N⟩ := Subtype.ext hx
  obtain rfl : y = ⟨jqNModC L N, jqNModC_mem L N⟩ := Subtype.ext hy
  refine CharPModel.place_eq_of_ord_pos_of_derivative_evalEval_ne_zero N dataN a b ?_ ?_ P Q hPj hPjN hQj hQjN
  · rw [evalEval_map_mapRingHom]
    exact hroot
  · rw [derivative_map, evalEval_map_mapRingHom]
    exact hder

theorem place_B_eq_of_centre (dataN : ModularPolynomialData N) (a b : L)
    (hroot : evalModularPair a b dataN.Φ = 0) (hder : evalModularPair a b (derivative dataN.Φ) ≠ 0)
    (P Q : Place L (modularFunctionFieldBar N))
    (hPj : 0 < P.ord (jB N - algebraMap L _ a)) (hPjN : 0 < P.ord (jNB N - algebraMap L _ b))
    (hQj : 0 < Q.ord (jB N - algebraMap L _ a)) (hQjN : 0 < Q.ord (jNB N - algebraMap L _ b)) :
    P = Q :=
  place_eq_of_centre_of_eq N (modularFunctionFieldBar_eq_modularFunctionFieldC N) dataN a b hroot hder
    (jB N) (jNB N) (coe_jB N) (coe_jNB N) P Q hPj hPjN hQj hQjN

theorem exists_centre_B (dataN : ModularPolynomialData N) (u : Place L (modularFunctionFieldBar N)) (a : L)
    (hu : 0 < u.ord (jB N - algebraMap L _ a)) :
    ∃ b : L, 0 < u.ord (jNB N - algebraMap L _ b) ∧ evalModularPair a b dataN.Φ = 0 ∧
      (evalModularPair (jB N) (jNB N) (derivative dataN.Φ) ≠ 0 →
        u.ord (evalModularPair (jB N) (jNB N) (derivative dataN.Φ)) = 0 →
        evalModularPair a b (derivative dataN.Φ) ≠ 0) := by
  have hrat := isRational_B N u
  have hjmem : (jB N : modularFunctionFieldBar N) ∈ u.toValuationSubring :=
    mem_of_ord_sub_algebraMap_pos u a (jB_sub_algebraMap_ne_zero N a) hu
  have hjNmem : (jNB N : modularFunctionFieldBar N) ∈ u.toValuationSubring := by
    have hint : IsIntegral u.toValuationSubring (jNB N : modularFunctionFieldBar N) :=
      ⟨phiAt dataN.Φ (⟨jB N, hjmem⟩ : u.toValuationSubring), phiAt_monic dataN.monic _, by
        rw [← eval_map, phiAt_map, eval_phiAt]
        exact evalModularPair_B_eq_zero N dataN⟩
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := u.toValuationSubring)
      (K := modularFunctionFieldBar N)).mp hint
    rw [← hy]
    exact y.2
  refine ⟨u.evalAt (jNB N : modularFunctionFieldBar N), ?_, ?_, ?_⟩
  · exact ord_sub_evalAt_pos u hrat hjNmem (jNB_sub_algebraMap_ne_zero N _)
  · exact evalModularPair_eq_zero_of_residue u hjmem hjNmem (residue_eq_algebraMap_of_ord_sub_pos u hjmem a hu)
      (residue_eq_algebraMap_of_ord_sub_pos u hjNmem _
        (ord_sub_evalAt_pos u hrat hjNmem (jNB_sub_algebraMap_ne_zero N _))) dataN.Φ
      (evalModularPair_B_eq_zero N dataN)
  · intro hne hord
    exact evalModularPair_ne_zero_of_ord_eq_zero u hjmem hjNmem (residue_eq_algebraMap_of_ord_sub_pos u hjmem a hu)
      (residue_eq_algebraMap_of_ord_sub_pos u hjNmem _
        (ord_sub_evalAt_pos u hrat hjNmem (jNB_sub_algebraMap_ne_zero N _))) (derivative dataN.Φ) hne hord

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N, squarefree_one]
  calc 0 < N / 1 := by rw [Nat.div_one]; exact Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
        Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem exists_place_B_of_root (dataN : ModularPolynomialData N) (a : L) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
    (hD : evalModularPair (jB N) (jNB N) (derivative dataN.Φ) ≠ 0)
    (hgood : ∀ u : Place L (modularFunctionFieldBar N), 0 < u.ord (jB N - algebraMap L _ a) →
      u.ord (evalModularPair (jB N) (jNB N) (derivative dataN.Φ)) = 0)
    (b : L) (hb : evalModularPair a b dataN.Φ = 0) :
    ∃ u : Place L (modularFunctionFieldBar N),
      0 < u.ord (jB N - algebraMap L _ a) ∧ 0 < u.ord (jNB N - algebraMap L _ b) := by
  classical
  have hfin : {u : Place L (modularFunctionFieldBar N) | 0 < u.ord (jB N - algebraMap L _ a)}.Finite :=
    (finite_ord_ne_zero_B N (jB_sub_algebraMap_ne_zero N a)).subset fun u hu => ne_of_gt hu
  set S := hfin.toFinset with hSdef
  have hS : ∀ u, u ∈ S ↔ 0 < u.ord (jB N - algebraMap L _ a) := fun u => by
    rw [hSdef, Set.Finite.mem_toFinset]
    rfl

  haveI : FiniteDimensional (IntermediateField.adjoin L ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
    Module.finite_of_finrank_pos (by rw [CompEq.finrank_adjoin_jBar_eq_dedekindPsi N]; exact dedekindPsi_pos N)
  have hsum := sum_ord_jBar_sub_eq_finrank N a S hS
  rw [CompEq.finrank_adjoin_jBar_eq_dedekindPsi N] at hsum
  have hone : ∀ u ∈ S, u.ord (jB N - algebraMap L _ a) = 1 := fun u hu =>
    ord_jBar_sub_eq_one_of_ne_zero_of_ne N u a ha0 ha1728 ((hS u).mp hu)
  have hcardS : S.card = dedekindPsi N := by
    have h1 : ∑ u ∈ S, u.ord (jB N - algebraMap L _ a) = (S.card : ℤ) := by
      rw [Finset.sum_congr rfl hone]
      simp
    have h2 : (S.card : ℤ) = (dedekindPsi N : ℤ) := h1.symm.trans hsum
    exact_mod_cast h2

  set R := (phiAt dataN.Φ a).roots.toFinset with hRdef
  have hRcard : R.card ≤ dedekindPsi N := by
    calc R.card ≤ (phiAt dataN.Φ a).roots.card := Multiset.toFinset_card_le _
      _ ≤ (phiAt dataN.Φ a).natDegree := card_roots' _
      _ = dedekindPsi N := by rw [dataN.monic.natDegree_map, dataN.natDegree_eq]
  have hmemR : ∀ c : L, c ∈ R ↔ evalModularPair a c dataN.Φ = 0 := fun c => by
    rw [hRdef, Multiset.mem_toFinset, mem_roots (phiAt_monic dataN.monic a).ne_zero, IsRoot.def, eval_phiAt]

  have hcentre : ∀ u ∈ S, ∃ c : L, 0 < u.ord (jNB N - algebraMap L _ c) ∧ evalModularPair a c dataN.Φ = 0 ∧
      evalModularPair a c (derivative dataN.Φ) ≠ 0 := fun u hu => by
    obtain ⟨c, hc, hΦ, hder⟩ := exists_centre_B N dataN u a ((hS u).mp hu)
    exact ⟨c, hc, hΦ, hder hD (hgood u ((hS u).mp hu))⟩
  choose! ctr hctr using hcentre
  have hmaps : ∀ u ∈ S, ctr u ∈ R := fun u hu => (hmemR _).mpr (hctr u hu).2.1
  have hinj : ∀ u₁ ∈ S, ∀ u₂ ∈ S, ctr u₁ = ctr u₂ → u₁ = u₂ := fun u₁ hu₁ u₂ hu₂ heq =>
    place_B_eq_of_centre N dataN a (ctr u₁) (hctr u₁ hu₁).2.1 (hctr u₁ hu₁).2.2 u₁ u₂
      ((hS u₁).mp hu₁) (hctr u₁ hu₁).1 ((hS u₂).mp hu₂) (heq ▸ (hctr u₂ hu₂).1)

  obtain ⟨u, hu, hub⟩ := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := R) (fun u _ => ctr u)
    (fun u hu => hmaps u hu) (fun u₁ u₂ hu₁ hu₂ h => hinj u₁ hu₁ u₂ hu₂ h) (by rw [hcardS]; exact hRcard)
    b ((hmemR b).mpr hb)
  refine ⟨u, (hS u).mp hu, ?_⟩
  rw [hub]
  exact (hctr u hu).1

theorem centre_smul (σ : L ≃ₐ[ℚ] L) (u : Place L (modularFunctionFieldBar N)) (a b : L)
    (hj : 0 < u.ord (jB N - algebraMap L _ a)) (hjN : 0 < u.ord (jNB N - algebraMap L _ b)) :
    0 < (arithmeticGalois (modularFunctionFieldFull N) σ • u).ord (jB N - algebraMap L _ (σ a)) ∧
      0 < (arithmeticGalois (modularFunctionFieldFull N) σ • u).ord (jNB N - algebraMap L _ (σ b)) := by
  set g := arithmeticGalois (modularFunctionFieldFull N) σ with hg
  have hgj : g • (jB N : modularFunctionFieldBar N) = jB N :=
    arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ (modularFunctionField_le_full N (jq_mem N))
  have hgjN : g • (jNB N : modularFunctionFieldBar N) = jNB N :=
    arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ (jqd_mem_full N (dvd_refl N))
  have hga : ∀ c : L, g • (algebraMap L (modularFunctionFieldBar N) c) = algebraMap L _ (σ c) := fun c => by
    rw [SemilinearAut.smul_algebraMap, hg, baseAut_arithmeticGalois]
    rfl
  constructor
  · have h := SemilinearAut.ord_smul g u (jB N - algebraMap L _ a)
    rw [smul_sub, hgj, hga] at h
    rw [h]
    exact hj
  · have h := SemilinearAut.ord_smul g u (jNB N - algebraMap L _ b)
    rw [smul_sub, hgjN, hga] at h
    rw [h]
    exact hjN

theorem derivPhi_B_ne_zero (dataN : ModularPolynomialData N) :
    evalModularPair (jB N) (jNB N) (derivative dataN.Φ) ≠ 0 := by
  intro h
  have hval := map_evalModularPair (modularFunctionFieldBar N).val.toRingHom (jB N) (jNB N) (derivative dataN.Φ)
  have hgen : (modularFunctionFieldBar N).val.toRingHom (jB N) = jqModC L := coe_jB N
  have hgenN : (modularFunctionFieldBar N).val.toRingHom (jNB N) = jqNModC L N := coe_jNB N
  rw [hgen, hgenN, h, map_zero] at hval
  set K₀ := IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)) with hK₀
  set jK : K₀ := ⟨jqModC L, IntermediateField.mem_adjoin_simple_self L (jqModC L)⟩ with hjK
  have haeval : aeval (jqNModC L N) (phiAt dataN.Φ jK) = 0 := by
    rw [aeval_def, ← eval_map, phiAt_map, show (algebraMap K₀ (LaurentSeries L)) jK = jqModC L from rfl,
      eval_phiAt]
    exact evalModularPair_jq_eq_zero L dataN
  have hint : IsIntegral K₀ (jqNModC L N) := ⟨phiAt dataN.Φ jK, phiAt_monic dataN.monic jK, haeval⟩
  have hmin : minpoly K₀ (jqNModC L N) = phiAt dataN.Φ jK := minpoly_jqNModC_eq L N dataN
  have hsep : (minpoly K₀ (jqNModC L N)).Separable := (minpoly.irreducible hint).separable
  have hne := hsep.aeval_derivative_ne_zero (minpoly.aeval K₀ (jqNModC L N))
  apply hne
  rw [hmin, derivative_phiAt, aeval_def, ← eval_map, phiAt_map,
    show (algebraMap K₀ (LaurentSeries L)) jK = jqModC L from rfl, eval_phiAt]
  exact hval.symm

end Upstairs

section Downstairs
variable {q : ℕ} [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] (N : ℕ) [NeZero N]

scoped instance isCurveOver_C : IsCurveOver k (modularFunctionFieldC k N) :=
  isCurveOver_modularFunctionFieldC_of_perfectField k N

theorem isRational_C (v : Place k (modularFunctionFieldC k N)) : v.IsRational := isRational_of_isCurveOver v

theorem finite_ord_ne_zero_C {f : modularFunctionFieldC k N} (hf : f ≠ 0) :
    {v : Place k (modularFunctionFieldC k N) | v.ord f ≠ 0}.Finite := finite_ord_ne_zero hf

theorem exists_isCentreOf_C (v : Place k (modularFunctionFieldC k N))
    (hj : 0 ≤ v.ord (jGeomGen k N)) (hjN : 0 ≤ v.ord (jNGeomGen k N)) :
    ∃ c : k × k, IsCentreOf k N c v := by
  have hj0 : jGeomGen k N ≠ 0 := by simpa using jGeomGen_sub_algebraMap_ne_zero k N 0
  have hjN0 : jNGeomGen k N ≠ 0 := by simpa using jNGeomGen_sub_algebraMap_ne_zero k N 0
  exact ⟨_, exists_isCentreOf_of_isRational (isRational_C k N v)
    ⟨v.mem_of_ord_nonneg hj0 hj, v.mem_of_ord_nonneg hjN0 hjN⟩⟩

variable {k N} in
theorem derivPhi_centre_ne_zero (dataN : ModularPolynomialData N) {c : k × k}
    {v : Place k (modularFunctionFieldC k N)} (hc : IsCentreOf k N c v)
    (hv : v.ord (evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ)) = 0)
    (hne : evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ) ≠ 0) :
    evalModularPair c.1 c.2 (derivative dataN.Φ) ≠ 0 :=
  evalModularPair_ne_zero_of_ord_eq_zero v hc.jGeomGen_mem hc.jNGeomGen_mem hc.residue_jGeomGen hc.residue_jNGeomGen
    (derivative dataN.Φ) hne hv

variable {k N} in

theorem derivPhi_C_ne_zero (hqN : ¬ q ∣ N) (dataN : ModularPolynomialData N) :
    evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ) ≠ 0 := by
  intro h
  have hval := map_evalModularPair (modularFunctionFieldC k N).val.toRingHom (jGeomGen k N) (jNGeomGen k N)
    (derivative dataN.Φ)
  have hgen : (modularFunctionFieldC k N).val.toRingHom (jGeomGen k N) = jqModC k := rfl
  have hgenN : (modularFunctionFieldC k N).val.toRingHom (jNGeomGen k N) = jqNModC k N := rfl
  rw [hgen, hgenN, h, map_zero] at hval
  set K₀ := IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)) with hK₀
  set jK : K₀ := ⟨jqModC k, IntermediateField.mem_adjoin_simple_self k (jqModC k)⟩ with hjK
  have hNk : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  have hsep : (minpoly K₀ (jqNModC k N)).Separable := isSeparable_jqNModC_of_natCast_ne_zero k N hNk
  have haeval : aeval (jqNModC k N) (phiAt dataN.Φ jK) = 0 := by
    rw [aeval_def, ← eval_map, phiAt_map, show (algebraMap K₀ (LaurentSeries k)) jK = jqModC k from rfl,
      eval_phiAt]
    exact evalModularPair_jq_eq_zero k dataN
  have hint : IsIntegral K₀ (jqNModC k N) := ⟨phiAt dataN.Φ jK, phiAt_monic dataN.monic jK, haeval⟩

  have hle : K₀ ≤ modularFunctionFieldC k N :=
    IntermediateField.adjoin.mono k _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hext : IntermediateField.extendScalars hle = (IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k))) := by
    have ejK : (algebraMap K₀ (LaurentSeries k)) jK = jqModC k := rfl
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ modularFunctionFieldC k N := hx
      have hle' : modularFunctionFieldC k N ≤ IntermediateField.restrictScalars k (IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k))) := by
        change IntermediateField.adjoin k {jqModC k, jqNModC k N} ≤ _
        rw [IntermediateField.adjoin_le_iff]
        rintro y (rfl | rfl)
        · show jqModC k ∈ IntermediateField.restrictScalars k (IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k)))
          rw [IntermediateField.mem_restrictScalars, ← ejK]
          exact ((IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k)))).algebraMap_mem jK
        · show jqNModC k N ∈ IntermediateField.restrictScalars k (IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k)))
          rw [IntermediateField.mem_restrictScalars]
          exact IntermediateField.mem_adjoin_simple_self (↥K₀) (jqNModC k N)
      have hx2 : x ∈ IntermediateField.restrictScalars k (IntermediateField.adjoin (↥K₀) ({jqNModC k N} : Set (LaurentSeries k))) := hle' hx'
      rwa [IntermediateField.mem_restrictScalars] at hx2
    · rw [IntermediateField.adjoin_simple_le_iff]
      show jqNModC k N ∈ modularFunctionFieldC k N
      exact jqNModC_mem k N
  have hdeg : (minpoly K₀ (jqNModC k N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint, ← (IntermediateField.equivOfEq hext).toLinearEquiv.finrank_eq,
      ← IntermediateField.relfinrank_eq_finrank_of_le hle]
    exact relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN
  have hmin : minpoly K₀ (jqNModC k N) = phiAt dataN.Φ jK := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (phiAt_monic dataN.monic jK)
      (minpoly.dvd K₀ _ haeval)
    rw [hdeg, dataN.monic.natDegree_map, dataN.natDegree_eq]
  have hne := hsep.aeval_derivative_ne_zero (minpoly.aeval K₀ (jqNModC k N))
  apply hne
  rw [hmin, derivative_phiAt, aeval_def, ← eval_map, phiAt_map,
    show (algebraMap K₀ (LaurentSeries k)) jK = jqModC k from rfl, eval_phiAt]
  exact hval.symm

end Downstairs

section Packet
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral L N q} {hβ : HeckeBetaBarIntegral L N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem isCentreOf_sp (u : Place L (modularFunctionFieldBar N)) (a b : A)
    (hj : 0 < u.ord (jB N - algebraMap L _ (a : L))) (hjN : 0 < u.ord (jNB N - algebraMap L _ (b : L))) :
    IsCentreOf k N (red a, red b) (P.sp u) :=
  ⟨P.d0_j u a hj, P.d0_jN u b hjN⟩

include P in
theorem exists_centre_lift (dataN : ModularPolynomialData N) (v : Place k (modularFunctionFieldC k N))
    {c : k × k} (hc : IsCentreOf k N c v) :
    ∃ a₀ b₀ : A, red a₀ = c.1 ∧ red b₀ = c.2 := by
  obtain ⟨w, hw⟩ := P.d4 v
  rcases forall_ord_jBar_sub_le_zero_or_exists_ord_pos A N dataN w with hpole | ⟨a, b, ha, hb⟩
  · exfalso
    have hneg := P.d0_j_pole w hpole
    rw [hw] at hneg
    have hnonneg : 0 ≤ v.ord (jGeomGen k N) := v.ord_nonneg_of_mem hc.jGeomGen_mem
    exact absurd hneg (not_lt.mpr hnonneg)
  · have hc' : IsCentreOf k N (red a, red b) v := hw ▸ isCentreOf_sp P w a b ha hb
    have h := hc.eq hc'
    exact ⟨a, b, by rw [h], by rw [h]⟩

end Packet

end ModularCurve.UnramifiedLift
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq.ModularCurve.UnramifiedLift"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq.ModularCurve"

open ModularCurve.UnramifiedLift in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∃ X : Finset (Place k (modularFunctionFieldC k N)),
      ∀ v : Place k (modularFunctionFieldC k N), v ∉ X →
        ∃ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          P.sp u = v ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull N) σ • u = u := by
  classical
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N

  obtain ⟨B, hBj, hBjN, hBuniq⟩ := exists_finset_place_eq_of_ord_jqModC_sub_pos k q N hqN
  have hNk : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  have hsep := isSeparable_jqNModC_of_natCast_ne_zero k N hNk

  have hDC0 : evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ) ≠ 0 :=
    derivPhi_C_ne_zero hqN dataN
  have hDB0 : evalModularPair (jB N) (jNB N) (derivative dataN.Φ) ≠ 0 := derivPhi_B_ne_zero N dataN

  have hZB : {z : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
      z.ord (evalModularPair (jB N) (jNB N) (derivative dataN.Φ)) ≠ 0}.Finite :=
    finite_ord_ne_zero_B N hDB0
  let badB : Set k := {t | ∃ z : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
    z.ord (evalModularPair (jB N) (jNB N) (derivative dataN.Φ)) ≠ 0 ∧
      ∃ a : A, 0 < z.ord (jB N - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) ∧ red a = t}
  have hbadB : badB.Finite := by
    refine (hZB.image (fun z => if h : ∃ a : A,
        0 < z.ord (jB N - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) then red h.choose else 0)).subset ?_
    rintro t ⟨z, hz, a, ha, rfl⟩
    refine ⟨z, hz, ?_⟩
    have hex : ∃ a : A, 0 < z.ord (jB N - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := ⟨a, ha⟩
    dsimp only
    rw [dif_pos hex]
    have hmem := mem_of_ord_sub_algebraMap_pos z (a : AlgebraicClosure ℚ) (jB_sub_algebraMap_ne_zero N _) ha
    have e1 := evalAt_eq_of_ord_sub_pos z (isRational_B N z) hmem (a : AlgebraicClosure ℚ) ha
    have e2 := evalAt_eq_of_ord_sub_pos z (isRational_B N z) hmem (hex.choose : AlgebraicClosure ℚ) hex.choose_spec
    rw [show hex.choose = a from Subtype.ext (e2.symm.trans e1)]
  let bad : Set k := ({0, red ((1728 : ℕ) : A)} : Set k) ∪ badB
  have hbad : bad.Finite := (Set.toFinite _).union hbadB

  have hX1 : (⋃ t ∈ bad, {v : Place k (modularFunctionFieldC k N) |
      0 < v.ord (jGeomGen k N - algebraMap k _ t)}).Finite :=
    hbad.biUnion fun t _ => finite_setOf_ord_jGeomGen_sub_pos k N hsep t
  have hX2 : {v : Place k (modularFunctionFieldC k N) |
      v.ord (evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ)) ≠ 0}.Finite :=
    finite_ord_ne_zero_C k N hDC0
  refine ⟨B ∪ hX1.toFinset ∪ hX2.toFinset, fun v hv => ?_⟩
  have hvB : v ∉ B := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hvX1 : v ∉ ⋃ t ∈ bad, {v : Place k (modularFunctionFieldC k N) |
      0 < v.ord (jGeomGen k N - algebraMap k _ t)} := fun h =>
    hv (Finset.mem_union_left _ (Finset.mem_union_right _ (hX1.mem_toFinset.mpr h)))
  have hvX2 : v.ord (evalModularPair (jGeomGen k N) (jNGeomGen k N) (derivative dataN.Φ)) = 0 := by
    by_contra h
    exact hv (Finset.mem_union_right _ (hX2.mem_toFinset.mpr h))

  have hj : 0 ≤ v.ord (jGeomGen k N) := not_lt.mp fun h => hvB (hBj v h)
  have hjN : 0 ≤ v.ord (jNGeomGen k N) := not_lt.mp fun h => hvB (hBjN v h)
  obtain ⟨c, hc⟩ := exists_isCentreOf_C k N v hj hjN
  have hc1 : c.1 ∉ bad := fun hmem => hvX1 (Set.mem_biUnion hmem hc.1)

  have hΦc : evalModularPair c.1 c.2 dataN.Φ = 0 := hc.modularEquation dataN
  have hDc : evalModularPair c.1 c.2 (derivative dataN.Φ) ≠ 0 := derivPhi_centre_ne_zero dataN hc hvX2 hDC0

  obtain ⟨a₀, b₀, ha₀, -⟩ := exists_centre_lift P dataN v hc
  obtain ⟨a', ha', hfix⟩ := exists_teichmuller q red a₀
  have hreda : red a' = c.1 := ha'.trans ha₀
  obtain ⟨b', hb'root, hredb, huniq⟩ :=
    exists_root_lift_phi red dataN.Φ dataN.monic a' c.2 (hreda ▸ hΦc) (hreda ▸ hDc)

  have hcoeA : ∀ (x y : A) (Ψ : Polynomial (Polynomial ℤ)),
      ((evalModularPair x y Ψ : A) : AlgebraicClosure ℚ) = evalModularPair (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ) Ψ :=
    fun x y Ψ => map_evalModularPair (algebraMap A (AlgebraicClosure ℚ)) x y Ψ
  have hder : evalModularPair (a' : AlgebraicClosure ℚ) (b' : AlgebraicClosure ℚ) (derivative dataN.Φ) ≠ 0 := by
    intro h
    apply hDc
    have h1 : evalModularPair a' b' (derivative dataN.Φ) = 0 := by
      apply Subtype.val_injective
      rw [hcoeA]
      exact h
    have h2 := map_evalModularPair red a' b' (derivative dataN.Φ)
    rw [h1, map_zero, hreda, hredb] at h2
    exact h2.symm

  have ha'0 : (a' : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    apply hc1
    left
    rw [← hreda, show a' = 0 from ZeroMemClass.coe_eq_zero.mp h, map_zero]
    exact Set.mem_insert _ _
  have ha'1728 : (a' : AlgebraicClosure ℚ) ≠ 1728 := by
    intro h
    apply hc1
    left
    have h' : a' = ((1728 : ℕ) : A) := by
      apply Subtype.ext
      rw [h, SubringClass.coe_natCast]
      norm_num
    rw [← hreda, h']
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hgood : ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < u.ord (jB N - algebraMap (AlgebraicClosure ℚ) _ (a' : AlgebraicClosure ℚ)) →
        u.ord (evalModularPair (jB N) (jNB N) (derivative dataN.Φ)) = 0 := by
    intro u hu
    by_contra hne
    exact hc1 (Or.inr ⟨u, hne, a', hu, hreda⟩)

  obtain ⟨u, huj, hujN⟩ := exists_place_B_of_root N dataN a' ha'0 ha'1728 hDB0 hgood b' hb'root
  refine ⟨u, ?_, ?_⟩
  · have hcu : IsCentreOf k N (red a', red b') (P.sp u) := isCentreOf_sp P u a' b' huj hujN
    rw [hreda, hredb] at hcu
    exact hBuniq v hvB (P.sp u) c.1 c.2 hc.1 hc.2 hcu.1 hcu.2
  · intro σ hσ
    obtain ⟨hσj, hσjN⟩ := centre_smul N σ u a' b' huj hujN
    rw [hfix σ hσ] at hσj
    have hσroot : evalModularPair (a' : AlgebraicClosure ℚ) (σ b') dataN.Φ = 0 :=
      root_smul dataN.Φ σ a' b' (hfix σ hσ) hb'root
    have hσmem : σ (b' : AlgebraicClosure ℚ) ∈ A := root_mem dataN.Φ dataN.monic a' _ hσroot
    have hsp : P.sp (arithmeticGalois (modularFunctionFieldFull N) σ • u) = P.sp u := P.d6_inertia σ hσ u
    have hc1' : IsCentreOf k N (red a', red ⟨σ b', hσmem⟩) (P.sp u) :=
      hsp ▸ isCentreOf_sp P _ a' ⟨σ b', hσmem⟩ hσj hσjN
    have hc2' : IsCentreOf k N (red a', red b') (P.sp u) := isCentreOf_sp P u a' b' huj hujN
    have hredσ : red ⟨σ b', hσmem⟩ = c.2 := by
      rw [← hredb]
      exact (Prod.ext_iff.mp (hc1'.eq hc2')).2
    have hσb : (⟨σ b', hσmem⟩ : A) = b' := huniq _ hσroot hredσ
    have hσb' : σ (b' : AlgebraicClosure ℚ) = b' := congrArg Subtype.val hσb
    rw [hσb'] at hσjN
    exact place_B_eq_of_centre N dataN a' b' hb'root hder _ u hσj hσjN huj hujN

end
end S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq (solution)
