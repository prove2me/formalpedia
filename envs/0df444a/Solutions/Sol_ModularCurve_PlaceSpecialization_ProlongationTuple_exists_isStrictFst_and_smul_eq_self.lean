-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isStrictFst_and_smul_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/69b086d1-53f8-58ad-af7b-47c54c9fd5fa

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple"

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple arithmeticGalois modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_one_apply jq coeff_jq_neg_one ModularPolynomialData jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ssPlaces jGeomGen jGeomGen_sub_algebraMap_ne_zero qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff atkinLehnerInvolutionFull cuspInftyBar cuspInftyBar_toValuationSubring arithmeticGalois_smul_geomAut hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple reduceFst reduceSnd IsStrictFst sp d0_j exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq reduceFst_atkinLehnerBar_smul reduceSnd_atkinLehnerBar_smul"
p2m_open "ModularCurve.PlaceSpecialization"

section General
variable {M : ℕ} [NeZero M]

theorem ord_cuspInftyBar_coeffEmb_qExpand_neg' (d : ℕ) [NeZero d]
    (hmem : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq) ∈ modularFunctionFieldBar M) :
    (cuspInftyBar M).ord (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), hmem⟩ : modularFunctionFieldBar M) < 0 := by
  set x : modularFunctionFieldBar M := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), hmem⟩ with hx
  have hc : (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar M) x).coeff ((d : ℤ) * (-1)) ≠ 0 := by
    show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).coeff _ ≠ 0
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have hne : x ≠ 0 := by
    intro h0; apply hc; rw [h0, qSeriesBar_zero, HahnSeries.coeff_zero]
  have hnot : x ∉ (cuspInftyBar M).toValuationSubring := by
    rw [cuspInftyBar_toValuationSubring, mem_qIntegersBar_iff, not_le]
    have hle := HahnSeries.order_le_of_coeff_ne_zero hc
    have hd : (0 : ℤ) < (d : ℤ) := by have := NeZero.ne d; omega
    nlinarith
  by_contra hge
  push_neg at hge
  exact hnot ((cuspInftyBar M).mem_of_ord_nonneg hne hge)

theorem exists_ord_pos_of_ord_neg (f : modularFunctionFieldBar M) (hf : f ≠ 0)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) (hV₀ : V₀.ord f < 0) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M), 0 < V.ord f := by
  classical
  obtain ⟨D, hD, hdeg⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional M).exists_divisor f hf
  by_contra hno
  push_neg at hno
  have hsum : Divisor.degree D = ∑ v ∈ D.support, D v := by
    show (Finsupp.liftAddHom _) D = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    show D v * ((v.deg : ℕ) : ℤ) = D v
    rw [deg_eq_one_modularFunctionFieldBar M v]
    simp
  have hmem : V₀ ∈ D.support := Finsupp.mem_support_iff.mpr (by rw [hD]; exact hV₀.ne)
  have hlt : ∑ v ∈ D.support, D v < 0 := by
    have h1 : ∑ v ∈ D.support, D v ≤ D V₀ := by
      rw [← Finset.add_sum_erase _ _ hmem]
      have : ∑ v ∈ D.support.erase V₀, D v ≤ 0 := Finset.sum_nonpos fun v _ => by rw [hD]; exact hno v
      linarith
    have h2 : D V₀ < 0 := by rw [hD]; exact hV₀
    omega
  rw [← hsum, hdeg] at hlt
  exact lt_irrefl _ hlt

end General

section Fibre
variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]
  (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

theorem frob_frob_ne_of_ord_sub_pos (v : Place k (modularFunctionFieldC k N)) (c : k) (hc : c ^ (q ^ 2) ≠ c)
    (h : 0 < v.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c)) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v := by
  intro hfix
  haveI : CharP (modularFunctionFieldC k N) q :=
    charP_of_injective_algebraMap (algebraMap k (modularFunctionFieldC k N)).injective q
  haveI : Fact (Nat.Prime q) := inferInstance
  set j : modularFunctionFieldC k N := jGeomGen k N with hj
  set φ := frobeniusGeomLevel k N data hKr with hφ
  set g : modularFunctionFieldC k N := j - algebraMap k (modularFunctionFieldC k N) c with hg
  set d : k := c ^ (q ^ 2) with hd
  set y : modularFunctionFieldC k N := j - algebraMap k (modularFunctionFieldC k N) d with hy
  have hg0 : g ≠ 0 := jGeomGen_sub_algebraMap_ne_zero k N c
  have hgmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg0 h.le
  have hgmax : (⟨g, hgmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
    v.mk_mem_maximalIdeal_of_ord_pos hgmem h

  have hcd : c - d ≠ 0 := sub_ne_zero.mpr (fun h' => hc (by rw [hd] at h'; exact h'.symm))
  have hymem : y ∈ v.toValuationSubring := by
    have := add_mem hgmem (v.algebraMap_mem' (c - d))
    have e : g + algebraMap k (modularFunctionFieldC k N) (c - d) = y := by rw [hg, hy, map_sub]; ring
    rwa [e] at this
  have hyunit : IsUnit (⟨y, hymem⟩ : v.toValuationSubring) := by
    by_contra hnu
    have hymax : (⟨y, hymem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hdiff := sub_mem hymax hgmax
    have e : (⟨y, hymem⟩ : v.toValuationSubring) - ⟨g, hgmem⟩ = algebraMap k v.toValuationSubring (c - d) := by
      apply Subtype.ext
      rw [Place.coe_algebraMap]
      show y - g = algebraMap k (modularFunctionFieldC k N) (c - d)
      rw [hy, hg, map_sub]; ring
    rw [e] at hdiff
    have hu : IsUnit (algebraMap k v.toValuationSubring (c - d)) := (hcd.isUnit).map _
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hdiff)) hu

  have hyinv : y⁻¹ ∈ v.toValuationSubring := by
    have h1 : v.toValuationSubring.valuation y = 1 := (v.toValuationSubring.valuation_eq_one_iff ⟨y, hymem⟩).mp hyunit
    apply (v.toValuationSubring.valuation_le_one_iff _).mp
    rw [map_inv₀, h1, inv_one]

  have hφj : φ j = j ^ q := frobeniusGeomLevel_jq k N data hKr
  have hφ2y : φ (φ y) = g ^ (q ^ 2) := by
    rw [hy, map_sub, map_sub, hφj, map_pow, hφj, AlgHom.commutes, AlgHom.commutes, ← pow_mul, ← sq, hg,
      sub_pow_char_pow, ← map_pow]

  have hmem2 : φ (φ y⁻¹) ∈ v.toValuationSubring := by
    have h1 := (mem_frobOnPlacesGeomLevel_iff k N data hKr (frobOnPlacesGeomLevel k N data hKr v) y⁻¹).mp
      (by rw [hfix]; exact hyinv)
    exact (mem_frobOnPlacesGeomLevel_iff k N data hKr v (φ y⁻¹)).mp h1
  rw [map_inv₀, map_inv₀, hφ2y] at hmem2

  have hpow : (⟨g, hgmem⟩ : v.toValuationSubring) ^ (q ^ 2) ∈ maximalIdeal v.toValuationSubring :=
    Ideal.pow_mem_of_mem _ hgmax _ (pow_pos (Fact.out : q.Prime).pos 2)
  have hgq0 : g ^ (q ^ 2) ≠ 0 := pow_ne_zero _ hg0
  have hone : (1 : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    have := Ideal.mul_mem_right (⟨(g ^ (q ^ 2))⁻¹, hmem2⟩ : v.toValuationSubring) _ hpow
    have e : (⟨g, hgmem⟩ : v.toValuationSubring) ^ (q ^ 2) * ⟨(g ^ (q ^ 2))⁻¹, hmem2⟩ = 1 :=
      Subtype.ext (by push_cast; exact mul_inv_cancel₀ hgq0)
    rwa [e] at this
  exact (IsLocalRing.maximalIdeal.isMaximal v.toValuationSubring).ne_top
    ((Ideal.eq_top_iff_one _).mpr hone)

end Fibre

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
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

end PlaceSpecialization

end ModularCurve

end

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.ModularCurve.PlaceSpecialization"

set_option maxHeartbeats 6400000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k) :
    ∃ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V₀ ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀) ∧
      P.reduceFst V₀ ∉ W := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨X, hX⟩ := exists_finset_forall_exists_sp_eq_forall_inertia_smul_eq P hqN

  let jt : modularFunctionFieldC k N := jGeomGen k N
  let S : Finset (Place k (modularFunctionFieldC k N)) := X ∪ W
  have hred_inf : (Set.range (red : A → k)).Infinite := by
    haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
    haveI : Infinite (ResidueField A) := IsAlgClosed.instInfinite
    have hsub : Set.range (R.redBar : ResidueField A → k) ⊆ Set.range (red : A → k) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨a, (R.redBar_residue a).symm⟩
    exact (Set.infinite_range_of_injective R.redBar.injective).mono hsub

  have hbad1 : {x : k | x ^ (q ^ 2) = x}.Finite := by
    have : {x : k | x ^ (q ^ 2) = x} ⊆ ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset : Set k) := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      have hq1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq1)]
      simp [hx]
    exact Set.Finite.subset (Finset.finite_toSet _) this

  have hbad2 : {x : k | ∃ v ∈ S, 0 < v.ord (jt - algebraMap k (modularFunctionFieldC k N) x)}.Finite := by
    have hsub : {x : k | ∃ v ∈ S, 0 < v.ord (jt - algebraMap k (modularFunctionFieldC k N) x)}
        ⊆ ⋃ v ∈ (S : Set (Place k (modularFunctionFieldC k N))),
            {x : k | 0 < v.ord (jt - algebraMap k (modularFunctionFieldC k N) x)} := by
      intro x hx
      obtain ⟨v, hvS, hvx⟩ := hx
      exact Set.mem_biUnion (Finset.mem_coe.mpr hvS) hvx
    refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet S) fun v _ => ?_) hsub

    refine Set.Subsingleton.finite ?_
    intro x hx x' hx'
    simp only [Set.mem_setOf_eq] at hx hx'
    by_contra hne
    have hm : (⟨_, v.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N x) hx.le⟩ : v.toValuationSubring)
        ∈ maximalIdeal v.toValuationSubring := v.mk_mem_maximalIdeal_of_ord_pos _ hx
    have hm' : (⟨_, v.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N x') hx'.le⟩ : v.toValuationSubring)
        ∈ maximalIdeal v.toValuationSubring := v.mk_mem_maximalIdeal_of_ord_pos _ hx'
    have hdiff := sub_mem hm' hm
    have e : (⟨_, v.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N x') hx'.le⟩ : v.toValuationSubring)
        - ⟨_, v.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N x) hx.le⟩
        = algebraMap k v.toValuationSubring (x - x') := by
      apply Subtype.ext
      rw [Place.coe_algebraMap]
      show (jt - algebraMap k (modularFunctionFieldC k N) x') - (jt - algebraMap k (modularFunctionFieldC k N) x)
        = algebraMap k (modularFunctionFieldC k N) (x - x')
      rw [map_sub]; ring
    rw [e] at hdiff
    have hu : IsUnit (algebraMap k v.toValuationSubring (x - x')) := ((sub_ne_zero.mpr hne).isUnit).map _
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hdiff)) hu

  obtain ⟨c, ⟨a, rfl⟩, hcbad⟩ := (hred_inf.diff (hbad1.union hbad2)).nonempty
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_and] at hcbad
  obtain ⟨hc1, hc2⟩ := hcbad

  let jN : modularFunctionFieldBar N := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
  let f : modularFunctionFieldBar N := jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
  have hmem1 : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) ∈ modularFunctionFieldBar N := by
    rw [qExpand_one_apply]; exact jN.2
  have hjNpole : (cuspInftyBar N).ord jN < 0 := by
    have h := ord_cuspInftyBar_coeffEmb_qExpand_neg' (M := N) 1 hmem1
    have e : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), hmem1⟩ : modularFunctionFieldBar N) = jN :=
      Subtype.ext (by show coeffEmb _ (qExpand ℚ 1 jq) = coeffEmb _ jq; rw [qExpand_one_apply])
    rwa [e] at h
  have hjNnot : jN ∉ (cuspInftyBar N).toValuationSubring := fun hm => by
    have := (cuspInftyBar N).ord_nonneg_of_mem hm
    omega
  have hfnot : f ∉ (cuspInftyBar N).toValuationSubring := fun hm => by
    apply hjNnot
    have := add_mem hm ((cuspInftyBar N).algebraMap_mem' (a : AlgebraicClosure ℚ))
    simpa [f] using this
  have hf0 : f ≠ 0 := fun h0 => hfnot (h0 ▸ zero_mem _)
  have hfpole : (cuspInftyBar N).ord f < 0 := by
    by_contra hge; push_neg at hge
    exact hfnot ((cuspInftyBar N).mem_of_ord_nonneg hf0 hge)
  obtain ⟨V, hV⟩ := exists_ord_pos_of_ord_neg f hf0 (cuspInftyBar N) hfpole

  set v := P.sp V with hv
  have hvord : 0 < v.ord (jt - algebraMap k (modularFunctionFieldC k N) (red a)) := P.d0_j V a hV

  have hvS : v ∉ S := fun hvS => hc2 v hvS hvord
  have hvfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v :=
    frob_frob_ne_of_ord_sub_pos data hKr v (red a) hc1 hvord

  have hvX : v ∉ X := fun h => hvS (Finset.mem_union_left _ h)
  obtain ⟨u, hu, hufix⟩ := hX v hvX
  obtain ⟨V₁, hstr, -, hred₂, hfix₁⟩ :=
    exists_isStrictSnd_restrictAlong_eq_forall_inertia_smul_eq P u (by rw [hu]; exact hvfix) hufix

  refine ⟨ProlongationTuple.atkinLehnerBar N q • V₁, ?_, ?_, ?_⟩
  · have h1 : P.reduceFst (ProlongationTuple.atkinLehnerBar N q • V₁) = P.reduceSnd V₁ :=
      reduceFst_atkinLehnerBar_smul P hqN V₁
    have h2 : P.reduceSnd (ProlongationTuple.atkinLehnerBar N q • V₁) = P.reduceFst V₁ :=
      reduceSnd_atkinLehnerBar_smul P hqN V₁
    refine ⟨?_, ?_⟩
    · rw [h1, h2]; exact hstr.1.symm
    · rw [h1]; exact hstr.2
  · intro σ hσ
    rw [arithmeticGalois_smul_atkinLehnerBar_smul, hfix₁ σ hσ]
  · rw [reduceFst_atkinLehnerBar_smul P hqN V₁, hred₂, hu]
    exact fun h => hvS (Finset.mem_union_right _ h)

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self (solution)
