-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c16069f9-cf8c-53b2-aa7a-d548a35c700e

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_ModularCurve_sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Theorems.Thm_ModularCurve_exists_finset_forall_isCentreOf_unique_ord_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section SupplyN_Fin

open AlgebraicCurve Module

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero jNGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsAffineGeomPlace sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldC_of_perfectField atkinLehnerInvolutionFull arithmeticGalois_smul_geomAut exists_finset_forall_isCentreOf_unique_ord_eq_one"
namespace BaseInertImpl
p2m_open "ModularCurve"

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]

theorem finite_lSpace [IsAlgClosed K] [IsCurveOver K F] {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by
      rw [IsCurveOver.deg_eq_one_of_isAlgClosed P]; norm_num
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := hRR D'
    have h0 : (0 : ℤ) ≤ (ell (Kc - D') : ℤ) := Int.natCast_nonneg _
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  haveI : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rcases eq_or_ne v P with rfl | hv
      · simp
      · simp [Finsupp.single_eq_of_ne hv]
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

end ModularCurve.BaseInertImpl
end SupplyN_Fin

section SupplyN_NF

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero jNGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsAffineGeomPlace sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldC_of_perfectField atkinLehnerInvolutionFull arithmeticGalois_smul_geomAut exists_finset_forall_isCentreOf_unique_ord_eq_one" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.eq_of_ord_jGeomGen_sub_pos
    (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (w : Place k (modularFunctionFieldC k N)) (a b : k)
    (ha : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a))
    (hb : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b)) : a = b := by
  by_contra hne
  have hm : ∀ (c : k), 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) →
      ∃ hy : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c ∈ w.toValuationSubring,
        (⟨_, hy⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
    intro c hc
    have hy : jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c ∈ w.toValuationSubring :=
      w.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N c) hc.le
    refine ⟨hy, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : w.ord (((hu.unit : w.toValuationSubringˣ) : w.toValuationSubring) :
        modularFunctionFieldC k N) = 0 := w.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    exact absurd h0 hc.ne'
  obtain ⟨h1, hm1⟩ := hm a ha
  obtain ⟨h2, hm2⟩ := hm b hb
  have hdiff := Ideal.sub_mem _ hm2 hm1
  have hval : ((⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) b, h2⟩ :
        w.toValuationSubring)
      - ⟨jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a, h1⟩)
      = algebraMap k w.toValuationSubring (a - b) := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap, map_sub]
    ring
  rw [hval] at hdiff
  have hunit : IsUnit (algebraMap k w.toValuationSubring (a - b)) :=
    (IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _
  exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (w : Place k (modularFunctionFieldC k N)) (a : k)
    (ha : 0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a)) :
    0 < (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ q)) := by
  have hq : q.Prime := Fact.out
  have hqpos : 0 < (q : ℤ) := by exact_mod_cast hq.pos
  obtain ⟨e, he, -, hord⟩ := ModularCurve.exists_ramification_frobenius k N data hKr w
  have hkey := hord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ q))
  rw [ModularCurve.frobeniusGeomLevel_jGeomGen_sub_pow k N data hKr a, ← zpow_natCast (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) q,
    Place.ord_zpow] at hkey
  have he' : 0 < (e : ℤ) := by exact_mod_cast he
  have hprod : 0 < (e : ℤ) * (frobOnPlacesGeomLevel k N data hKr w).ord
      (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (a ^ q)) := by
    rw [← hkey]; exact mul_pos hqpos ha
  exact pos_of_mul_pos_right hprod he'.le

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.exists_ord_jGeomGen_sub_pos
    (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]
    [IsCurveOver k (modularFunctionFieldC k N)] (v₀ : Place k (modularFunctionFieldC k N))
    (a : k) : ∃ w : Place k (modularFunctionFieldC k N),
      0 < w.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) := by
  classical

  have hC : ConstantsAreBase k (modularFunctionFieldC k N) :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  have hpole : ∃ v : Place k (modularFunctionFieldC k N), v.ord (jGeomGen k N) < 0 := by
    by_contra hno
    push Not at hno
    have hmem : (jGeomGen k N : modularFunctionFieldC k N)
        ∈ LSpace (0 : Divisor k (modularFunctionFieldC k N)) := by
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun v => ?_
      rw [Finsupp.coe_zero, Pi.zero_apply, neg_zero]
      exact hno v
    rw [show LSpace (0 : Divisor k (modularFunctionFieldC k N)) = _ from hC] at hmem
    obtain ⟨c, hc⟩ := hmem
    apply jGeomGen_sub_algebraMap_ne_zero k N c
    rw [← hc, Algebra.linearMap_apply, sub_self]
  obtain ⟨v₁, hv₁⟩ := hpole
  have hne := jGeomGen_sub_algebraMap_ne_zero k N a
  have hxa : v₁.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) < 0 := by
    have hnotmem : (jGeomGen k N : modularFunctionFieldC k N) ∉ v₁.toValuationSubring :=
      fun hmem => not_lt.mpr (v₁.ord_nonneg_of_mem hmem) hv₁
    by_contra hge
    push Not at hge
    have hmem := v₁.mem_of_ord_nonneg hne hge
    have := add_mem hmem (v₁.algebraMap_mem' a)
    rw [sub_add_cancel] at this
    exact hnotmem this
  haveI hPD : HasPrincipalDivisors k (modularFunctionFieldC k N) := IsCurveOver.hasPrincipalDivisors
  obtain ⟨D, hD, hdeg⟩ := hPD.exists_divisor
    (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) a) hne
  by_contra hall
  push Not at hall
  have hall' : ∀ v, 0 ≤ (-D) v := fun v => by
    rw [Finsupp.neg_apply, neg_nonneg, hD v]; exact hall v
  have hv₀ : 0 < (-D) v₁ := by
    rw [Finsupp.neg_apply, neg_pos, hD v₁]; exact hxa
  have hmem : v₁ ∈ (-D).support := Finsupp.mem_support_iff.mpr hv₀.ne'
  have hdegsum : Divisor.degree (-D) = ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single (-D), Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v ((-D) v)
  have hdegpos : 0 < Divisor.degree (-D) := by
    rw [hdegsum]
    calc (0 : ℤ) < (-D) v₁ * (v₁.deg : ℤ) := by
          rw [IsCurveOver.deg_eq_one_of_isAlgClosed v₁, Nat.cast_one, mul_one]; exact hv₀
      _ ≤ ∑ v ∈ (-D).support, (-D) v * (v.deg : ℤ) :=
          Finset.single_le_sum (fun v _ => mul_nonneg (hall' v) (Int.natCast_nonneg _)) hmem
  rw [map_neg, hdeg, neg_zero] at hdegpos
  exact lt_irrefl 0 hdegpos

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.infinite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_ne
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    [IsCurveOver k (modularFunctionFieldC k N)] (v₀ : Place k (modularFunctionFieldC k N)) :
    {w : Place k (modularFunctionFieldC k N) |
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w}.Infinite := by
  classical
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le
  choose z hz using ModularCurve.exists_ord_jGeomGen_sub_pos k N v₀
  have hinf : Set.Infinite {a : k | a ^ (q ^ 2) ≠ a} := by
    have hfin : Set.Finite {a : k | a ^ (q ^ 2) = a} := by
      have hP : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := by
        apply FiniteField.X_pow_card_sub_X_ne_zero k
        calc 1 < 2 := by norm_num
          _ ≤ q := hq2
          _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      refine ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.finite_toSet).subset ?_
      intro a ha
      simp only [Set.mem_setOf_eq] at ha
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ha, sub_self]
    have huniv : (Set.univ : Set k).Infinite := Set.infinite_univ_iff.mpr inferInstance
    have : {a : k | a ^ (q ^ 2) ≠ a} = Set.univ \ {a : k | a ^ (q ^ 2) = a} := by
      ext a; simp
    rw [this]
    exact huniv.diff hfin
  have hzinj : Set.InjOn z {a : k | a ^ (q ^ 2) ≠ a} := fun a _ b _ hab =>
    ModularCurve.eq_of_ord_jGeomGen_sub_pos k N (z a) a b (hz a) (hab ▸ hz b)
  have hmaps : Set.MapsTo z {a : k | a ^ (q ^ 2) ≠ a}
      {w | frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w} := by
    intro a ha hfix
    simp only [Set.mem_setOf_eq] at ha hfix
    have h1 := ModularCurve.ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos q k N data hKr _ _
      (ModularCurve.ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos q k N data hKr _ _ (hz a))
    rw [hfix, ← pow_mul, ← pow_two] at h1
    exact ha (ModularCurve.eq_of_ord_jGeomGen_sub_pos k N (z a) _ _ h1 (hz a))
  exact Set.infinite_of_injOn_mapsTo hzinj hmaps hinf

end SupplyN_NF

section SupplyN

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero jNGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsAffineGeomPlace sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldC_of_perfectField atkinLehnerInvolutionFull arithmeticGalois_smul_geomAut exists_finset_forall_isCentreOf_unique_ord_eq_one"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd sp d2 d1 d4 ProlongationTuple.atkinLehnerBar ProlongationTuple exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq reduceFst_atkinLehnerBar_smul reduceSnd_atkinLehnerBar_smul"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

theorem arithmeticGalois_smul_atkinLehnerBar_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (ProlongationTuple.atkinLehnerBar N q • W)
      = ProlongationTuple.atkinLehnerBar N q • (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • W) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  ext1
  ext x
  simp only [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]

  have key : ∀ y : modularFunctionFieldBar (N * q),
      (ProlongationTuple.atkinLehnerBar N q)⁻¹ • ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ)⁻¹ • y)
        = (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)⁻¹ • ((ProlongationTuple.atkinLehnerBar N q)⁻¹ • y) := by
    intro y
    have h := arithmeticGalois_smul_geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ⁻¹
      (atkinLehnerInvolutionFull N q)⁻¹ y
    rw [map_inv, map_inv] at h
    rw [AlgEquiv.smul_def]
    show _ = (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)⁻¹ • ((ProlongationTuple.atkinLehnerBar N q)⁻¹ y)
    exact h.symm ▸ rfl
  constructor
  · intro hx; rw [key] at hx; exact hx
  · intro hx; rw [key]; exact hx

theorem exists_isStrictSnd_reduceSnd_eq
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) :
    ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd U ∧ P.reduceSnd U = v := by
  obtain ⟨w, hw⟩ := P.d4 v
  have hguard : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w))
      ≠ P.sp w := by rw [hw]; exact hv
  obtain ⟨W₀, hW₀β, hW₀α, -, -⟩ := P.d2 w hguard
  refine ⟨W₀, ⟨?_, ?_⟩, ?_⟩
  · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
      = frobOnPlacesGeomLevel k N data hKr
          (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
    rw [hW₀α, hW₀β]
  · show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)))
      ≠ P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    rw [hW₀β]; exact hguard
  · show P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = v
    rw [hW₀β, hw]

theorem exists_isStrictFst_frobOnPlacesGeomLevel_reduceFst_eq
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) :
    ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst U ∧ frobOnPlacesGeomLevel k N data hKr (P.reduceFst U) = v := by
  classical
  set φ : Place k (modularFunctionFieldC k N) → Place k (modularFunctionFieldC k N) :=
    frobOnPlacesGeomLevel k N data hKr with hφdef
  have hq : q.Prime := Fact.out
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨w, hw⟩ := P.d4 v
  have hguard : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w))
      ≠ P.sp w := by rw [hw]; exact hv
  obtain ⟨W₀, hW₀β, hW₀α, hW₀e, huniq⟩ := P.d2 w hguard
  have hsum := ModularCurve.sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one N q hqN hβ
    (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q)) w
  have hW₀mem : W₀ ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ w :=
    Place.mem_fiberAlong.mpr hW₀β
  obtain ⟨U, hUmem, hUne⟩ : ∃ U ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ w,
      U ≠ W₀ := by
    by_contra hcon
    push Not at hcon
    have hfib : Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ w = {W₀} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hW₀mem, hcon⟩
    rw [hfib, Finset.sum_singleton, hW₀e] at hsum
    norm_num at hsum
    have : (q : ℤ) = 0 := by linarith
    exact hq.ne_zero (by exact_mod_cast this)
  have hUβ : U.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w :=
    Place.mem_fiberAlong.mp hUmem
  rcases P.d1 U with h1 | h1
  · exact absurd (huniq U hUβ (by rw [h1, hUβ])) hUne
  · refine ⟨U, ⟨?_, ?_⟩, ?_⟩
    · show frobOnPlacesGeomLevel k N data hKr
          (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα))
        = P.sp (U.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
      exact h1
    · intro h2
      apply hv
      have h3 : φ (P.reduceFst U) = v := by
        show frobOnPlacesGeomLevel k N data hKr
          (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)) = v
        rw [h1, hUβ, hw]
      have h2' : φ (φ (P.reduceFst U)) = P.reduceFst U := h2
      calc φ (φ v) = φ (φ (φ (P.reduceFst U))) := by rw [h3]
        _ = φ (P.reduceFst U) := by rw [h2']
        _ = v := h3
    · show frobOnPlacesGeomLevel k N data hKr
          (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)) = v
      rw [h1, hUβ, hw]

end ModularCurve.PlaceSpecialization
end SupplyN

section SupplyN_Main

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero jNGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsAffineGeomPlace sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCurveOver_modularFunctionFieldC_of_perfectField atkinLehnerInvolutionFull arithmeticGalois_smul_geomAut exists_finset_forall_isCentreOf_unique_ord_eq_one"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd sp d2 d1 d4 ProlongationTuple.atkinLehnerBar ProlongationTuple exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq reduceFst_atkinLehnerBar_smul reduceSnd_atkinLehnerBar_smul"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option maxHeartbeats 25600000 in

theorem exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq_impl
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hWne : W.Nonempty)
    (B : Finset (Place k (modularFunctionFieldC k N)))
    (Kc : Divisor k (modularFunctionFieldC k N)) (g₀ : ℕ)
    (hRR : ∀ D : Divisor k (modularFunctionFieldC k N),
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀) :
    ∃ (d₁ d₂ : ℕ)
      (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (T₁ T₂ : Finset (Place k (modularFunctionFieldC k N)))
      (Qs : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      d₁ + 1 = g₀ + W.card ∧ d₂ = g₀ ∧
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v) ∧
      (∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v) ∧
      Disjoint T₁ W ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, IsAffineGeomPlace k N v) ∧ (∀ v ∈ T₂, IsAffineGeomPlace k N v) ∧
      (∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
        (∀ w ∈ W, w.HasValue h 0) → h = 0) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
        ∃ c : k, h = algebraMap k (modularFunctionFieldC k N) c) ∧
      P.IsStrictFst Qs ∧ (∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i)) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) := by
  classical
  haveI hIC : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  obtain ⟨w₀, hw₀⟩ := hWne

  set NF : Set (Place k (modularFunctionFieldC k N)) :=
    {w | frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w} with hNFdef
  have hNF : NF.Infinite :=
    ModularCurve.infinite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_ne q k N data hKr w₀
  set S₁ : Set (Place k (modularFunctionFieldC k N)) :=
    {t | ∃ U, P.IsStrictFst U ∧ P.reduceFst U = t ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U}
    with hS₁def
  set S₂ : Set (Place k (modularFunctionFieldC k N)) :=
    {t | ∃ U, P.IsStrictSnd U ∧ P.reduceSnd U = t ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U}
    with hS₂def

  obtain ⟨X, hX⟩ := exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq P hqN
  have hNFX : (NF \ (↑X : Set (Place k (modularFunctionFieldC k N)))).Infinite := hNF.diff X.finite_toSet
  have key₂ : ∀ v ∈ NF \ (↑X : Set (Place k (modularFunctionFieldC k N))),
      ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.IsStrictSnd V ∧ P.reduceSnd V = v ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V := by
    rintro v ⟨hv, hvX⟩
    obtain ⟨u, hu, hufix⟩ := hX v hvX
    obtain ⟨V, hstr, -, hred, hfix⟩ :=
      exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq P u (by rw [hu]; exact hv) hufix
    exact ⟨V, hstr, by rw [hred, hu], hfix⟩
  have hS₂ : S₂.Infinite := hNFX.mono fun v hv => key₂ v hv
  obtain ⟨v₁, hv₁⟩ := hNFX.nonempty
  obtain ⟨U₁, -, -, -⟩ := key₂ v₁ hv₁
  haveI : Nonempty (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := ⟨U₁⟩
  have hS₁ : S₁.Infinite := by
    refine hNFX.mono fun v hv => ?_
    obtain ⟨V, hstr, hred, hfix⟩ := key₂ v hv
    refine ⟨ProlongationTuple.atkinLehnerBar N q • V, ?_, ?_, ?_⟩
    · have h1 : P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V) = P.reduceSnd V :=
        reduceFst_atkinLehnerBar_smul P hqN V
      have h2 : P.reduceSnd (ProlongationTuple.atkinLehnerBar N q • V) = P.reduceFst V :=
        reduceSnd_atkinLehnerBar_smul P hqN V
      refine ⟨?_, ?_⟩
      · rw [h1, h2]; exact hstr.1.symm
      · rw [h1]; exact hstr.2
    · rw [reduceFst_atkinLehnerBar_smul P hqN V, hred]
    · intro σ hσ
      rw [arithmeticGalois_smul_atkinLehnerBar_smul, hfix σ hσ]

  set NA : Set (Place k (modularFunctionFieldC k N)) := {v | ¬ IsAffineGeomPlace k N v} with hNAdef
  have hj0 : (jGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jGeomGen_sub_algebraMap_ne_zero k N 0
  have hjN0 : (jNGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jNGeomGen_sub_algebraMap_ne_zero k N 0
  haveI hPD : HasPrincipalDivisors k (modularFunctionFieldC k N) := IsCurveOver.hasPrincipalDivisors
  have hNA : NA.Finite := by
    obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen k N) hj0
    obtain ⟨DN, hDN, -⟩ := hPD.exists_divisor (jNGeomGen k N) hjN0
    refine (Dj.support.finite_toSet.union DN.support.finite_toSet).subset ?_
    intro v hv
    rw [hNAdef, Set.mem_setOf_eq, IsAffineGeomPlace, not_and_or] at hv
    rcases hv with h | h
    · left
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hDj]
      intro h0
      exact h (v.mem_of_ord_nonneg hj0 (le_of_eq h0.symm))
    · right
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hDN]
      intro h0
      exact h (v.mem_of_ord_nonneg hjN0 (le_of_eq h0.symm))

  obtain ⟨Xs, hXs⟩ := ModularCurve.exists_finset_forall_isCentreOf_unique_ord_eq_one q k N hqN
  have hNAX : (NA ∪ (↑Xs : Set (Place k (modularFunctionFieldC k N)))).Finite := hNA.union Xs.finite_toSet

  obtain ⟨T₂, hT₂S, hT₂card, hT₂ell⟩ :=
    AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Kc g₀ hRR Kc ((S₂ \ (NA ∪ (↑Xs : Set (Place k (modularFunctionFieldC k N))))) \ ↑B)
      ((hS₂.diff hNAX).diff B.finite_toSet)
  obtain ⟨T₁, hT₁S, hT₁card, hT₁ell⟩ :=
    AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Kc g₀ hRR
      (Kc + ∑ w ∈ W, Finsupp.single w 1) (((S₁ \ ↑W) \ (NA ∪ (↑Xs : Set (Place k (modularFunctionFieldC k N))))) \ ↑B)
      (((hS₁.diff W.finite_toSet).diff hNAX).diff B.finite_toSet)

  have hC : ConstantsAreBase k (modularFunctionFieldC k N) :=
    constantsAreBase_of_deg_eq_one w₀ (IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
  have hell0 : ell (0 : Divisor k (modularFunctionFieldC k N)) = 1 :=
    ell_zero_eq_one_of_constantsAreBase hC
  have hellK : ell Kc = g₀ := by
    have h := hRR 0
    rw [sub_zero, hell0, map_zero] at h
    push_cast at h
    omega
  have hdegK : Divisor.degree Kc = 2 * (g₀ : ℤ) - 2 := by
    have h := hRR Kc
    rw [sub_self, hell0, hellK] at h
    push_cast at h
    omega
  have hSW : ∀ u, (∑ w ∈ W, Finsupp.single w (1 : ℤ) : Divisor k (modularFunctionFieldC k N)) u
      = if u ∈ W then 1 else 0 := by
    intro u
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hdegW : Divisor.degree (∑ w ∈ W, Finsupp.single w (1 : ℤ) : Divisor k (modularFunctionFieldC k N))
      = (W.card : ℤ) := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  have hellKW : ell (Kc + ∑ w ∈ W, Finsupp.single w 1) + 1 = g₀ + W.card := by
    have h := hRR (Kc + ∑ w ∈ W, Finsupp.single w 1)
    have hneg : ell (Kc - (Kc + ∑ w ∈ W, Finsupp.single w 1)) = 0 := by
      rw [sub_add_cancel_left, ell, lSpace_eq_bot_of_degree_neg, finrank_bot]
      rw [map_neg, hdegW, neg_lt_zero]
      exact_mod_cast Finset.card_pos.mpr ⟨w₀, hw₀⟩
    rw [hneg, map_add, hdegK, hdegW] at h
    push_cast at h
    have hWpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨w₀, hw₀⟩
    omega

  have hl₁ : ∀ t ∈ T₁, ∃ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst Q ∧ P.reduceFst Q = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q = Q :=
    fun t ht => (hT₁S ht).1.1.1
  have hl₂ : ∀ t ∈ T₂, ∃ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd Q ∧ P.reduceSnd Q = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q = Q :=
    fun t ht => (hT₂S ht).1.1
  choose! L₁ hL₁ using hl₁
  choose! L₂ hL₂ using hl₂
  have hT₁NA : ∀ v ∈ T₁, IsAffineGeomPlace k N v := fun v hv => by
    by_contra h; exact (hT₁S hv).1.2 (Or.inl h)
  have hT₂NA : ∀ v ∈ T₂, IsAffineGeomPlace k N v := fun v hv => by
    by_contra h; exact (hT₂S hv).1.2 (Or.inl h)
  have hT₁Xs : ∀ v ∈ T₁, v ∉ Xs := fun v hv hx => (hT₁S hv).1.2 (Or.inr hx)
  have hT₂Xs : ∀ v ∈ T₂, v ∉ Xs := fun v hv hx => (hT₂S hv).1.2 (Or.inr hx)

  obtain ⟨ts, hts⟩ := (hS₁.diff T₁.finite_toSet).nonempty
  obtain ⟨⟨Qs, hQs, hQsred, -⟩, htsT⟩ := hts
  refine ⟨T₁.card, T₂.card, fun i => L₁ (T₁.equivFin.symm i), fun j => L₂ (T₂.equivFin.symm j),
    T₁, T₂, Qs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hQs, ?_, ?_, ?_⟩
  · rw [hT₁card]; exact hellKW
  · rw [hT₂card, hellK]
  · intro i; exact (hL₁ _ (T₁.equivFin.symm i).2).1
  · intro j; exact (hL₂ _ (T₂.equivFin.symm j).2).1
  · intro i j hij
    have h : P.reduceFst (L₁ (T₁.equivFin.symm i)) = P.reduceFst (L₁ (T₁.equivFin.symm j)) := hij
    rw [(hL₁ _ (T₁.equivFin.symm i).2).2.1, (hL₁ _ (T₁.equivFin.symm j).2).2.1] at h
    exact T₁.equivFin.symm.injective (Subtype.ext h)
  · intro i j hij
    have h : P.reduceSnd (L₂ (T₂.equivFin.symm i)) = P.reduceSnd (L₂ (T₂.equivFin.symm j)) := hij
    rw [(hL₂ _ (T₂.equivFin.symm i).2).2.1, (hL₂ _ (T₂.equivFin.symm j).2).2.1] at h
    exact T₂.equivFin.symm.injective (Subtype.ext h)
  · intro v
    constructor
    · intro hv
      refine ⟨T₁.equivFin ⟨v, hv⟩, ?_⟩
      rw [(hL₁ _ (T₁.equivFin.symm _).2).2.1, Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      rw [(hL₁ _ (T₁.equivFin.symm i).2).2.1]
      exact (T₁.equivFin.symm i).2
  · intro v
    constructor
    · intro hv
      refine ⟨T₂.equivFin ⟨v, hv⟩, ?_⟩
      rw [(hL₂ _ (T₂.equivFin.symm _).2).2.1, Equiv.symm_apply_apply]
    · rintro ⟨j, rfl⟩
      rw [(hL₂ _ (T₂.equivFin.symm j).2).2.1]
      exact (T₂.equivFin.symm j).2
  · exact Finset.disjoint_left.mpr fun v hv hvW => (hT₁S hv).1.1.2 hvW
  · exact Finset.disjoint_left.mpr fun v hv hvB => (hT₁S hv).2 hvB
  · exact Finset.disjoint_left.mpr fun v hv hvB => (hT₂S hv).2 hvB
  · exact hT₁NA
  · exact hT₂NA
  · exact fun v hv => hXs v (hT₁Xs v hv) (hT₁NA v hv)
  · exact fun v hv => hXs v (hT₂Xs v hv) (hT₂NA v hv)
  ·
    intro h hreg hsimple hval
    by_contra h0
    set D : Divisor k (modularFunctionFieldC k N) :=
      ∑ v ∈ T₁, Finsupp.single v 1 - ∑ w ∈ W, Finsupp.single w 1 with hDdef
    have hST : ∀ u, (∑ v ∈ T₁, Finsupp.single v (1 : ℤ) : Divisor k (modularFunctionFieldC k N)) u
        = if u ∈ T₁ then 1 else 0 := by
      intro u
      rw [Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hDapp : ∀ u, D u = (if u ∈ T₁ then 1 else 0) - (if u ∈ W then 1 else 0) := by
      intro u; rw [hDdef, Finsupp.sub_apply, hST, hSW]
    have hdisj : ∀ u, u ∈ W → u ∉ T₁ := fun u huW huT =>
      (hT₁S huT).1.1.2 huW
    have hordW : ∀ w ∈ W, 1 ≤ w.ord h := by
      intro w hw
      obtain ⟨hm, hres⟩ := hval w hw
      rw [map_zero, IsLocalRing.residue_eq_zero_iff] at hres
      have hnu : ¬ IsUnit (⟨h, hm⟩ : w.toValuationSubring) :=
        (IsLocalRing.mem_maximalIdeal _).mp hres
      have hnn := w.ord_nonneg_of_mem hm
      by_contra hlt
      have h00 : w.ord h = 0 := by omega
      obtain ⟨hm', hu⟩ := w.exists_isUnit_of_ord_eq_zero h0 h00
      exact hnu hu
    have hmem : h ∈ LSpace D := by
      rw [mem_lSpace_iff_ord]
      refine Or.inr fun u => ?_
      rw [hDapp]
      by_cases huW : u ∈ W
      · rw [if_neg (hdisj u huW), if_pos huW]; have := hordW u huW; omega
      · by_cases huT : u ∈ T₁
        · rw [if_pos huT, if_neg huW]; have := hsimple u huT; omega
        · rw [if_neg huT, if_neg huW]; have := hreg u huT; omega
    have hdegT : Divisor.degree (∑ v ∈ T₁, Finsupp.single v (1 : ℤ) : Divisor k (modularFunctionFieldC k N))
        = (T₁.card : ℤ) := by
      rw [map_sum]
      simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hdegD : Divisor.degree D = (T₁.card : ℤ) - W.card := by
      rw [hDdef, map_sub, hdegT, hdegW]
    have hKD : Kc - D = Kc + ∑ w ∈ W, Finsupp.single w 1 - ∑ v ∈ T₁, Finsupp.single v 1 := by
      rw [hDdef, sub_sub_eq_add_sub]
    have hellD : ell D = 0 := by
      have h1 := hRR D
      rw [hKD, hT₁ell, hdegD, hT₁card] at h1
      push_cast at h1
      have h3 : ((ell (Kc + ∑ w ∈ W, Finsupp.single w 1) : ℕ) : ℤ) + 1 = g₀ + W.card := by
        exact_mod_cast hellKW
      omega
    have hfin : Module.Finite k (LSpace D) := by
      exact ModularCurve.BaseInertImpl.finite_lSpace hRR w₀ D
    have hbot : (⊥ : Submodule k (modularFunctionFieldC k N)) = LSpace D :=
      Submodule.eq_of_le_of_finrank_eq bot_le (by rw [finrank_bot]; exact hellD.symm)
    rw [← hbot, Submodule.mem_bot] at hmem
    exact h0 hmem
  ·
    intro h hreg hsimple
    set D : Divisor k (modularFunctionFieldC k N) := ∑ v ∈ T₂, Finsupp.single v 1 with hDdef
    have hDapp : ∀ u, D u = if u ∈ T₂ then 1 else 0 := by
      intro u
      rw [hDdef, Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
    have hmem : h ∈ LSpace D := by
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne h 0 with rfl | h0
      · exact Or.inl rfl
      · refine Or.inr fun u => ?_
        rw [hDapp]
        split_ifs with hu
        · have := hsimple u hu; omega
        · have := hreg u hu; omega
    have hdeg : Divisor.degree D = (T₂.card : ℤ) := by
      rw [hDdef, map_sum]
      simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hellD : ell D = 1 := by
      have h1 := hRR D
      have h2 : Kc - D = Kc - ∑ v ∈ T₂, Finsupp.single v 1 := rfl
      rw [hdeg, hT₂card, hellK, h2, hT₂ell] at h1
      push_cast at h1
      omega
    have hle : LinearMap.range (Algebra.linearMap k (modularFunctionFieldC k N)) ≤ LSpace D := by
      rintro _ ⟨c, rfl⟩
      refine lSpace_mono (D := 0) ?_ (algebraMap_mem_lSpace_zero c)
      intro u
      rw [hDapp]
      split_ifs <;> simp
    have hfin : Module.Finite k (LSpace D) := by
      exact ModularCurve.BaseInertImpl.finite_lSpace hRR w₀ D
    have heq : LinearMap.range (Algebra.linearMap k (modularFunctionFieldC k N)) = LSpace D := by
      apply Submodule.eq_of_le_of_finrank_eq hle
      rw [LinearMap.finrank_range_of_inj (algebraMap k (modularFunctionFieldC k N)).injective,
        Module.finrank_self]
      exact hellD.symm
    rw [← heq] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  · intro i h
    rw [hQsred, (hL₁ _ (T₁.equivFin.symm i).2).2.1] at h
    exact htsT (by rw [Finset.mem_coe, h]; exact (T₁.equivFin.symm i).2)
  · intro i σ hσ
    exact (hL₁ _ (T₁.equivFin.symm i).2).2.2 σ hσ
  · intro j σ hσ
    exact (hL₂ _ (T₂.equivFin.symm j).2).2.2 σ hσ

end ModularCurve.PlaceSpecialization
end SupplyN_Main

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hWne : W.Nonempty)
    (B : Finset (Place k (modularFunctionFieldC k N)))
    (Kc : Divisor k (modularFunctionFieldC k N)) (g₀ : ℕ)
    (hRR : ∀ D : Divisor k (modularFunctionFieldC k N),
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀) :
    ∃ (d₁ d₂ : ℕ)
      (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (T₁ T₂ : Finset (Place k (modularFunctionFieldC k N)))
      (Qs : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      d₁ + 1 = g₀ + W.card ∧ d₂ = g₀ ∧
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v) ∧
      (∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v) ∧
      Disjoint T₁ W ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, IsAffineGeomPlace k N v) ∧ (∀ v ∈ T₂, IsAffineGeomPlace k N v) ∧
      (∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
        (∀ w ∈ W, w.HasValue h 0) → h = 0) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
        ∃ c : k, h = algebraMap k (modularFunctionFieldC k N) c) ∧
      P.IsStrictFst Qs ∧ (∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i)) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) :=
  ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq_impl P hqN W hWne B Kc g₀ hRR

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq.ModularCurve in

theorem _p2m_restate_check
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hWne : W.Nonempty)
    (B : Finset (Place k (modularFunctionFieldC k N)))
    (Kc : Divisor k (modularFunctionFieldC k N)) (g₀ : ℕ)
    (hRR : ∀ D : Divisor k (modularFunctionFieldC k N),
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g₀) :
    ∃ (d₁ d₂ : ℕ)
      (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (T₁ T₂ : Finset (Place k (modularFunctionFieldC k N)))
      (Qs : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      d₁ + 1 = g₀ + W.card ∧ d₂ = g₀ ∧
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v) ∧
      (∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v) ∧
      Disjoint T₁ W ∧ Disjoint T₁ B ∧ Disjoint T₂ B ∧
      (∀ v ∈ T₁, IsAffineGeomPlace k N v) ∧ (∀ v ∈ T₂, IsAffineGeomPlace k N v) ∧
      (∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
        (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
        (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
          v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1)) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
        (∀ w ∈ W, w.HasValue h 0) → h = 0) ∧
      (∀ h : modularFunctionFieldC k N,
        (∀ v, v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
        ∃ c : k, h = algebraMap k (modularFunctionFieldC k N) c) ∧
      P.IsStrictFst Qs ∧ (∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i)) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) :=
  solution P hqN W hWne B Kc g₀ hRR

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq (solution)
