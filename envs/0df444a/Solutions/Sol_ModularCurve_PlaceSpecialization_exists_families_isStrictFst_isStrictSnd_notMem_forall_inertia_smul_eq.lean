-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8a876a48-6479-529b-b0fb-10c4b35df672

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jGeomGen_sub_algebraMap_ne_zero frobeniusGeomLevel_jGeomGen_sub_pow atkinLehnerInvolutionFull cuspZeroBar isCurveOver_modularFunctionFieldC_of_perfectField arithmeticGalois_smul_geomAut"
namespace KAux
p2m_open "ModularCurve"

section KAux_NF

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq.ModularCurve"

private theorem eq_of_ord_jGeomGen_sub_pos'
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

private theorem ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos'
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

private theorem exists_ord_jGeomGen_sub_pos'
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

private theorem infinite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_ne'
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    [IsCurveOver k (modularFunctionFieldC k N)] (v₀ : Place k (modularFunctionFieldC k N)) :
    {w : Place k (modularFunctionFieldC k N) |
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w}.Infinite := by
  classical
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le
  choose z hz using exists_ord_jGeomGen_sub_pos' k N v₀
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
    eq_of_ord_jGeomGen_sub_pos' k N (z a) a b (hz a) (hab ▸ hz b)
  have hmaps : Set.MapsTo z {a : k | a ^ (q ^ 2) ≠ a}
      {w | frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w} := by
    intro a ha hfix
    simp only [Set.mem_setOf_eq] at ha hfix
    have h1 := ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos' q k N data hKr _ _
      (ord_frobOnPlacesGeomLevel_jGeomGen_sub_pow_pos' q k N data hKr _ _ (hz a))
    rw [hfix, ← pow_mul, ← pow_two] at h1
    exact ha (eq_of_ord_jGeomGen_sub_pos' k N (z a) _ _ h1 (hz a))
  exact Set.infinite_of_injOn_mapsTo hzinj hmaps hinf

end KAux_NF

end ModularCurve.KAux

section KAux_AL

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "arithmeticGalois modularFunctionFieldBar ModularPolynomialData modularFunctionFieldFull modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence jGeomGen jGeomGen_sub_algebraMap_ne_zero frobeniusGeomLevel_jGeomGen_sub_pow atkinLehnerInvolutionFull cuspZeroBar isCurveOver_modularFunctionFieldC_of_perfectField arithmeticGalois_smul_geomAut"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd sp ProlongationTuple.atkinLehnerBar ProlongationTuple exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq reduceFst_atkinLehnerBar_smul reduceSnd_atkinLehnerBar_smul"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

omit [NeZero N] in

private theorem arithmeticGalois_smul_atkinLehnerBar_smul' (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
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

end ModularCurve.PlaceSpecialization

end KAux_AL

set_option maxHeartbeats 3200000 in
open ModularCurve.KAux _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (B : Finset (Place k (modularFunctionFieldC k N))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ i, P.reduceFst (Q₁ i) ∉ B) ∧ (∀ j, P.reduceSnd (Q₂ j) ∉ B) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI hIC : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N

  let v₀ : Place k (modularFunctionFieldC k N) := P.sp (cuspZeroBar N)
  set NF : Set (Place k (modularFunctionFieldC k N)) :=
    {w | frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w} with hNFdef
  have hNF : NF.Infinite := infinite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_ne' q k N data hKr v₀

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
    exact ⟨V, hstr, by rw [← hu]; exact hred, hfix⟩
  have key₁ : ∀ v ∈ NF \ (↑X : Set (Place k (modularFunctionFieldC k N))),
      ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.IsStrictFst U ∧ P.reduceFst U = v ∧
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U := by
    intro v hv
    obtain ⟨V, hstr, hred, hfix⟩ := key₂ v hv
    have h1 : P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V) = P.reduceSnd V :=
      reduceFst_atkinLehnerBar_smul P hqN V
    have h2 : P.reduceSnd (ProlongationTuple.atkinLehnerBar N q • V) = P.reduceFst V :=
      reduceSnd_atkinLehnerBar_smul P hqN V
    refine ⟨ProlongationTuple.atkinLehnerBar N q • V, ⟨?_, ?_⟩, ?_, ?_⟩
    · show frobOnPlacesGeomLevel k N data hKr (P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V))
        = P.reduceSnd (ProlongationTuple.atkinLehnerBar N q • V)
      rw [h1, h2]
      exact (show P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) from hstr.1).symm
    · show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
          (P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V)))
        ≠ P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V)
      rw [h1]
      exact (show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V))
        ≠ P.reduceSnd V from hstr.2)
    · show P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V) = v
      rw [h1]; exact hred
    · intro σ hσ
      rw [arithmeticGalois_smul_atkinLehnerBar_smul', hfix σ hσ]

  set S₁ : Set (Place k (modularFunctionFieldC k N)) :=
    {t | ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst U ∧ P.reduceFst U = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U} with hS₁def
  set S₂ : Set (Place k (modularFunctionFieldC k N)) :=
    {t | ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd U ∧ P.reduceSnd U = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • U = U} with hS₂def
  have hS₁ : (S₁ \ (↑B : Set (Place k (modularFunctionFieldC k N)))).Infinite :=
    (hNFX.mono fun v hv => key₁ v hv).diff B.finite_toSet
  have hS₂ : (S₂ \ (↑B : Set (Place k (modularFunctionFieldC k N)))).Infinite :=
    (hNFX.mono fun v hv => key₂ v hv).diff B.finite_toSet
  obtain ⟨T₁, hT₁S, hT₁card⟩ := hS₁.exists_subset_card_eq m₁
  obtain ⟨T₂, hT₂S, hT₂card⟩ := hS₂.exists_subset_card_eq m₂
  have hl₁ : ∀ t ∈ T₁, ∃ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst Q ∧ P.reduceFst Q = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q = Q :=
    fun t ht => (hT₁S (Finset.mem_coe.mpr ht)).1
  have hl₂ : ∀ t ∈ T₂, ∃ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictSnd Q ∧ P.reduceSnd Q = t ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q = Q :=
    fun t ht => (hT₂S (Finset.mem_coe.mpr ht)).1
  have hB₁ : ∀ t ∈ T₁, t ∉ B := fun t ht => (hT₁S (Finset.mem_coe.mpr ht)).2
  have hB₂ : ∀ t ∈ T₂, t ∉ B := fun t ht => (hT₂S (Finset.mem_coe.mpr ht)).2
  obtain ⟨v₁, hv₁⟩ := hNFX.nonempty
  obtain ⟨U₁, -, -, -⟩ := key₂ v₁ hv₁
  haveI : Nonempty (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := ⟨U₁⟩
  choose! L₁ hL₁ using hl₁
  choose! L₂ hL₂ using hl₂
  let e₁ := T₁.equivFinOfCardEq hT₁card
  let e₂ := T₂.equivFinOfCardEq hT₂card
  refine ⟨fun i => L₁ (e₁.symm i), fun j => L₂ (e₂.symm j), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact (hL₁ _ (e₁.symm i).2).1
  · intro j; exact (hL₂ _ (e₂.symm j).2).1
  · intro i j hij
    have h : P.reduceFst (L₁ (e₁.symm i)) = P.reduceFst (L₁ (e₁.symm j)) := hij
    rw [(hL₁ _ (e₁.symm i).2).2.1, (hL₁ _ (e₁.symm j).2).2.1] at h
    exact e₁.symm.injective (Subtype.ext h)
  · intro i j hij
    have h : P.reduceSnd (L₂ (e₂.symm i)) = P.reduceSnd (L₂ (e₂.symm j)) := hij
    rw [(hL₂ _ (e₂.symm i).2).2.1, (hL₂ _ (e₂.symm j).2).2.1] at h
    exact e₂.symm.injective (Subtype.ext h)
  · intro i
    rw [(hL₁ _ (e₁.symm i).2).2.1]; exact hB₁ _ (e₁.symm i).2
  · intro j
    rw [(hL₂ _ (e₂.symm j).2).2.1]; exact hB₂ _ (e₂.symm j).2
  · intro i; exact (hL₁ _ (e₁.symm i).2).2.2
  · intro j; exact (hL₂ _ (e₂.symm j).2).2.2

end S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq (solution)
