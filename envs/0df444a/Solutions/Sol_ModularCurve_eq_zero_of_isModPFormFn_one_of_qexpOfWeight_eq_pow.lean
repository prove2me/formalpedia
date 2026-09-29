-- Prove2me | solution 1 for ModularCurve.eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/868e58ee-bb1a-5e11-aa4c-e614d1a79b12

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
import Theorems.Thm_ModularCurve_ord_jqModC_census_of_char_three
import Theorems.Thm_ModularCurve_thetaL_jqModC_pow_mul_prod_sq_eq
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "ModularCurve~coeffMap_injective AlgebraicCurve"

namespace KATZ2C

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem _root_.KATZ2C.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "KATZ2C" "mem_of_ord_nonneg"

theorem ord_eq_zero_of_isUnit {f : F} (hf : f ∈ v.toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)) : v.ord f = 0 := by
  have := v.ord_coe_unit hu.unit
  simpa using this

theorem isUnit_algebraMap_mk {a : K} (ha : a ≠ 0) :
    IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
  refine ⟨⟨⟨algebraMap K F a, v.algebraMap_mem' a⟩, ⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩,
    ?_, ?_⟩, rfl⟩
  · refine Subtype.ext ?_
    show algebraMap K F a * algebraMap K F a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  · refine Subtype.ext ?_
    show algebraMap K F a⁻¹ * algebraMap K F a = 1
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]

theorem ord_algebraMap {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 :=
  ord_eq_zero_of_isUnit v (v.algebraMap_mem' a) (isUnit_algebraMap_mk v ha)

theorem ord_neg' (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [neg_eq_neg_one_mul, v.ord_mul (by norm_num) hf,
    show (-1 : F) = algebraMap K F (-1) by rw [map_neg, map_one],
    ord_algebraMap v (by norm_num), zero_add]

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_prod {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_add_eq_zero_of_ord_pos_of_isUnit {x d : F} (hx : x ∈ v.toValuationSubring)
    (hxpos : 0 < v.ord x) (hd : d ∈ v.toValuationSubring)
    (hdu : IsUnit (⟨d, hd⟩ : v.toValuationSubring)) : v.ord (x + d) = 0 := by
  have hxm : (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    v.mk_mem_maximalIdeal_of_ord_pos hx hxpos
  refine ord_eq_zero_of_isUnit v (add_mem hx hd) ?_

  set du := hdu.unit with hdu_def
  have hsum : (⟨x + d, add_mem hx hd⟩ : v.toValuationSubring) =
      (du : v.toValuationSubring) * (1 - -(((du⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring)
        * ⟨x, hx⟩)) := by
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
    refine Subtype.ext ?_
    simp only [hdu_def, IsUnit.unit_spec]
    show x + d = d + x
    ring
  rw [hsum]
  refine (Units.isUnit du).mul (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_)
  rw [← IsLocalRing.mem_maximalIdeal]
  exact neg_mem (Ideal.mul_mem_left _ _ hxm)

theorem ord_sub_algebraMap_of_ord_neg {t : F} (ht : v.ord t < 0) (a : K) :
    v.ord (t - algebraMap K F a) = v.ord t := by
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hinv : 0 < v.ord t⁻¹ := by rw [v.ord_inv]; omega
  have hinvmem : t⁻¹ ∈ v.toValuationSubring := v.mem_of_ord_nonneg (inv_ne_zero ht0) hinv.le

  have hw : t - algebraMap K F a = t * (-(algebraMap K F a * t⁻¹) + 1) := by
    field_simp
    ring
  have hmem : algebraMap K F a * t⁻¹ ∈ v.toValuationSubring :=
    mul_mem (v.algebraMap_mem' a) hinvmem
  have hunit : v.ord (-(algebraMap K F a * t⁻¹) + 1) = 0 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    refine ord_add_eq_zero_of_ord_pos_of_isUnit v (neg_mem hmem) ?_ (one_mem _) ?_
    · rw [ord_neg' v, v.ord_mul ((map_ne_zero _).mpr ha) (inv_ne_zero ht0), ord_algebraMap v ha,
        zero_add]
      exact hinv
    · exact ⟨1, Subtype.ext rfl⟩
  have hne : (-(algebraMap K F a * t⁻¹) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit

    have : t - algebraMap K F a = 0 := by rw [hw, h, mul_zero]
    have hta : t = algebraMap K F a := sub_eq_zero.mp this
    rcases eq_or_ne a 0 with rfl | ha
    · exact ht0 (by simpa using hta)
    · rw [hta, ord_algebraMap v ha] at ht
      exact lt_irrefl _ ht
  rw [hw, v.ord_mul ht0 hne, hunit, add_zero]

theorem ord_sub_algebraMap_of_ne {t : F} {j₀ : K} (hmem : t ∈ v.toValuationSubring)
    (hpos : 0 < v.ord (t - algebraMap K F j₀)) {a : K} (ha : a ≠ j₀) :
    v.ord (t - algebraMap K F a) = 0 := by
  have hsplit : t - algebraMap K F a = (t - algebraMap K F j₀) + algebraMap K F (j₀ - a) := by
    rw [map_sub]; ring
  rw [hsplit]
  have hja : j₀ - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  exact ord_add_eq_zero_of_ord_pos_of_isUnit v (sub_mem hmem (v.algebraMap_mem' _)) hpos
    (v.algebraMap_mem' _) (isUnit_algebraMap_mk v hja)

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).surjective

theorem eq_zero_of_forall_ord_nonneg_of_ord_pos [HasPrincipalDivisors K F] (v₀ : Place K F)
    (hdeg : v₀.deg ≠ 0) {g : F} (hord : ∀ w : Place K F, 0 ≤ w.ord g) (hpos : 0 < v₀.ord g) :
    g = 0 := by
  by_contra hg
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hpos
  have hDnonneg : ∀ w, 0 ≤ D w := fun w => by rw [hD w]; exact hord w
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hsum : Divisor.degree D = ∑ w ∈ D.support, D w * (w.deg : ℤ) := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    rfl
  have hposdeg : 0 < Divisor.degree D := by
    rw [hsum]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ w ∈ D.support, D w * (w.deg : ℤ) :=
          Finset.single_le_sum (fun w _ => mul_nonneg (hDnonneg w) (Int.natCast_nonneg _)) hmem
  omega

theorem exists_finset_ord_pos [HasPrincipalDivisors K F] {g : F} (hg : g ≠ 0) :
    ∃ S : Finset (Place K F), ∀ w, w ∈ S ↔ 0 < w.ord g := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  refine ⟨D.support.filter fun w => 0 < D w, fun w => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD w]
  exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩

end Toolkit

section Integrality

variable {K : Type*} [Field K] {X : IntermediateField K (LaurentSeries K)}

theorem mem_of_isIntegral_adjoin (v : Place K X) (t y : X) (ht : t ∈ v.toValuationSubring)
    (hint : IsIntegral (Algebra.adjoin K ({(t : LaurentSeries K)} : Set (LaurentSeries K)))
      (y : LaurentSeries K)) :
    y ∈ v.toValuationSubring := by
  classical

  obtain ⟨P, hPmon, hPeval⟩ := hint
  set R := Algebra.adjoin K ({(t : LaurentSeries K)} : Set (LaurentSeries K)) with hR
  set P₁ : Polynomial (LaurentSeries K) := P.map (algebraMap R (LaurentSeries K)) with hP₁
  have hP₁mon : P₁.Monic := hPmon.map _
  have hP₁eval : P₁.eval (y : LaurentSeries K) = 0 := by
    rw [hP₁, Polynomial.eval_map]; exact hPeval

  have hRmap : R = Subalgebra.map X.val (Algebra.adjoin K ({t} : Set X)) := by
    rw [hR, ← Algebra.adjoin_image, Set.image_singleton, IntermediateField.coe_val]

  have hle : ∀ c ∈ Algebra.adjoin K ({t} : Set X), c ∈ v.toValuationSubring := by
    intro c hc
    induction hc using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; exact hz ▸ ht
    | algebraMap r => exact v.algebraMap_mem' r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

  set ι : v.toValuationSubring →+* LaurentSeries K :=
    (X.val : X →+* LaurentSeries K).comp v.toValuationSubring.subtype with hι
  have hlifts : P₁ ∈ Polynomial.lifts ι := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have hcn : P₁.coeff n ∈ R := by
      rw [hP₁, Polynomial.coeff_map]
      exact (P.coeff n).2
    rw [hRmap] at hcn
    obtain ⟨c', hc', hcc'⟩ := hcn
    exact ⟨⟨c', hle c' hc'⟩, hcc'⟩
  obtain ⟨P₂, hP₂map, -, hP₂mon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hP₁mon

  have hyint : IsIntegral v.toValuationSubring y := by
    refine ⟨P₂, hP₂mon, ?_⟩
    have hinj : Function.Injective (X.val : X → LaurentSeries K) := by
      rw [IntermediateField.coe_val]; exact Subtype.val_injective
    apply hinj
    have h1 : X.val (Polynomial.eval₂ (algebraMap v.toValuationSubring X) y P₂) =
        P₂.eval₂ ι (y : LaurentSeries K) := by
      show (X.val : X →+* LaurentSeries K) (Polynomial.eval₂ _ y P₂) = _
      rw [Polynomial.hom_eval₂]; rfl
    rw [h1, ← Polynomial.eval_map, hP₂map, hP₁eval, map_zero]
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyint
  rw [← hz]
  exact z.2

end Integrality

section Level

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]

abbrev FN : Type _ := ↥(modularFunctionFieldC K N)

abbrev jj : FN K N := jGeomGen K N

theorem coe_jj : ((jj K N : FN K N) : LaurentSeries K) = jqModC K := rfl

theorem jj_ne_zero : jj K N ≠ 0 := by
  intro h
  have := congrArg (fun x : FN K N => (x : LaurentSeries K)) h
  simp only [coe_jj, ZeroMemClass.coe_zero] at this
  exact ModularCurve.jqModC_ne_zero_def K this

scoped instance instIsCurveOver : IsCurveOver K (FN K N) :=
  ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField K N

scoped instance instHasPrincipalDivisors : HasPrincipalDivisors K (FN K N) :=
  IsCurveOver.hasPrincipalDivisors

theorem ord_cusp (f : FN K N) :
    (cuspInftyGeom K N).ord f = HahnSeries.order (f : LaurentSeries K) :=
  ModularCurve.ord_qInftyPlaceMod K (jqModC_mem K N) f

theorem ord_cusp_jj : (cuspInftyGeom K N).ord (jj K N) = -1 := ModularCurve.ord_cuspInftyGeom_jq K N

theorem deg_cusp_ne_zero : (cuspInftyGeom K N).deg ≠ 0 := by
  rw [ModularCurve.deg_cuspInftyGeom]; exact one_ne_zero

variable {K N}

theorem place_cases (v : Place K (FN K N)) :
    (v.ord (jj K N) < 0 ∧ ∀ a : K, v.ord (jj K N - algebraMap K (FN K N) a) = v.ord (jj K N)) ∨
    (jj K N ∈ v.toValuationSubring ∧ ∃ j₀ : K, 0 < v.ord (jj K N - algebraMap K (FN K N) j₀) ∧
      ∀ a : K, a ≠ j₀ → v.ord (jj K N - algebraMap K (FN K N) a) = 0) := by
  rcases lt_or_ge (v.ord (jj K N)) 0 with hneg | hnonneg
  · exact Or.inl ⟨hneg, fun a => ord_sub_algebraMap_of_ord_neg v hneg a⟩
  · right
    have hmem : jj K N ∈ v.toValuationSubring := v.mem_of_ord_nonneg (jj_ne_zero K N) hnonneg
    refine ⟨hmem, v.evalAt (jj K N), ?_, fun a ha => ?_⟩
    · exact ModularCurve.ord_sub_evalAt_pos_of_isRational (isRational_of_isAlgClosed v) hmem
        (jGeomGen_sub_algebraMap_ne_zero K N _)
    · exact ord_sub_algebraMap_of_ne v hmem
        (ModularCurve.ord_sub_evalAt_pos_of_isRational (isRational_of_isAlgClosed v) hmem
          (jGeomGen_sub_algebraMap_ne_zero K N _)) ha

theorem inv_jj_mem_of_ord_neg {v : Place K (FN K N)} (h : v.ord (jj K N) < 0) :
    (jj K N)⁻¹ ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg (inv_ne_zero (jj_ne_zero K N)) (by rw [v.ord_inv]; omega)

theorem mem_of_isModPFormFn_of_jj_mem {G : FN K N} (hG : IsModPFormFn K 1 (G : LaurentSeries K))
    {v : Place K (FN K N)} (hv : jj K N ∈ v.toValuationSubring) :
    G ^ 6 * jj K N ^ 4 * (jj K N - algebraMap K (FN K N) 1728) ^ 3 ∈ v.toValuationSubring := by
  refine mem_of_isIntegral_adjoin v (jj K N) _ hv ?_
  have h := hG.1
  simp only [mul_one] at h
  convert h using 2 <;> first | rfl | (funext x; rfl) | simp

theorem mem_of_isModPFormFn_of_inv_jj_mem {G : FN K N} (hG : IsModPFormFn K 1 (G : LaurentSeries K))
    {v : Place K (FN K N)} (hv : (jj K N)⁻¹ ∈ v.toValuationSubring) :
    G ^ 2 * jj K N * (jj K N - algebraMap K (FN K N) 1728) ∈ v.toValuationSubring := by
  refine mem_of_isIntegral_adjoin v (jj K N)⁻¹ _ hv ?_
  have h := hG.2
  simp only [pow_one] at h
  convert h using 2 <;> first | rfl | (funext x; rfl) | simp

end Level

section Ramification

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N]

theorem ord_sub_dvd_jWidth_aux (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3) (hN : (N : K) ≠ 0)
    (X : IntermediateField K (LaurentSeries K)) (hX : X = modularFunctionFieldFullC K N)
    (hj : jqModC K ∈ X) [HasPrincipalDivisors K X]
    (v : Place K X) (j₀ : K) (hv : 0 < v.ord ((⟨jqModC K, hj⟩ : X) - algebraMap K X j₀)) :
    ∃ d : ℕ, v.ord ((⟨jqModC K, hj⟩ : X) - algebraMap K X j₀) = d ∧ d ∣ jWidth j₀ := by
  subst hX

  obtain ⟨S, hS⟩ := exists_finset_ord_pos (K := K)
    (g := (⟨jqModC K, hj⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ j₀)
    (by
      intro h
      rw [h] at hv
      simp at hv)

  let E₀ : WeierstrassCurve K := WeierstrassCurve.ofJ j₀
  have hE₀ : E₀.j = j₀ := WeierstrassCurve.ofJ_j j₀
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC K N hN j₀ E₀ hE₀ S
      hS
  obtain ⟨H, hH⟩ := hf2 v ((hS v).mpr hv)
  refine ⟨Nat.card {H' // f H' = f H}, ?_, ?_⟩
  · rw [← hH]; exact hf4 H
  · have := WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap h2 h3 E₀ N f hf3 H
    rwa [hE₀] at this

theorem ord_sub_dvd_jWidth (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N)
    (v : Place K (FN K N)) (j₀ : K) (hv : 0 < v.ord (jj K N - algebraMap K (FN K N) j₀)) :
    ∃ d : ℕ, v.ord (jj K N - algebraMap K (FN K N) j₀) = d ∧ d ∣ jWidth j₀ := by
  have hchar : ringChar K = p := ringChar.eq K p
  have h2 : ringChar K ≠ 2 := by rw [hchar]; omega
  have h3 : ringChar K ≠ 3 := by rw [hchar]; omega
  have hN : (N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p N]; exact hpN
  exact ord_sub_dvd_jWidth_aux h2 h3 hN (modularFunctionFieldC K N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN) (jqModC_mem K N) v j₀ hv

theorem ord_jj_le_six_aux [CharP K 3] (hN : (N : K) ≠ 0)
    (X : IntermediateField K (LaurentSeries K)) (hX : X = modularFunctionFieldFullC K N)
    (hj : jqModC K ∈ X) [HasPrincipalDivisors K X]
    (v : Place K X) (hv : 0 < v.ord (⟨jqModC K, hj⟩ : X)) :
    v.ord (⟨jqModC K, hj⟩ : X) ≤ 6 := by
  subst hX
  obtain ⟨S, hS⟩ := exists_finset_ord_pos (K := K) (g := (⟨jqModC K, hj⟩ : ↥(modularFunctionFieldFullC K N)))
    (by
      intro h
      rw [h] at hv
      simp at hv)
  obtain ⟨hcases, -, -⟩ := ModularCurve.ord_jqModC_census_of_char_three K N hN S hS
  rcases hcases v ((hS v).mpr hv) with h | h | h | h <;> omega

theorem ord_jj_le_six [CharP K 3] (h3N : ¬ 3 ∣ N) (v : Place K (FN K N)) (hv : 0 < v.ord (jj K N)) :
    v.ord (jj K N) ≤ 6 := by
  have hN : (N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 3 N]; exact h3N
  exact ord_jj_le_six_aux hN (modularFunctionFieldC K N)
    (ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K 3 N h3N) (jqModC_mem K N) v hv

end Ramification

section QSeries

variable (K : Type*) [Field K]

theorem coeff_thetaJ (k : ℤ) : (thetaJ K).coeff k = k • (jqModC K).coeff k := by
  rw [thetaJ, thetaL_apply]
  exact ModularCurve.theta_coeff (jqModC K) k

theorem coeff_thetaJ_neg_one : (thetaJ K).coeff (-1) = -1 := by
  rw [coeff_thetaJ, ModularCurve.coeff_jqModC_neg_one, neg_one_zsmul]

theorem thetaJ_ne_zero : thetaJ K ≠ 0 := by
  intro h
  have := coeff_thetaJ_neg_one K
  rw [h, HahnSeries.coeff_zero] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem order_thetaJ : (thetaJ K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [coeff_thetaJ_neg_one]; norm_num)) ?_
  by_contra hlt
  have hlt' : (thetaJ K).order < -1 := lt_of_not_ge hlt
  have hne : (thetaJ K).coeff (thetaJ K).order ≠ 0 :=
    mt HahnSeries.coeff_order_eq_zero.mp (thetaJ_ne_zero K)
  apply hne
  rw [coeff_thetaJ]
  have : (jqModC K).coeff (thetaJ K).order = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [ModularCurve.order_jqModC_def]
    exact hlt'
  rw [this, smul_zero]

theorem order_jqModC_sub_C (a : K) : (jqModC K - HahnSeries.C a).order = -1 := by
  have hC : ∀ k : ℤ, k ≠ 0 → (HahnSeries.C a : LaurentSeries K).coeff k = 0 := fun k hk => by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hk]
  have hcoeff : (jqModC K - HahnSeries.C a).coeff (-1) = 1 := by
    rw [HahnSeries.coeff_sub, ModularCurve.coeff_jqModC_neg_one, hC (-1) (by norm_num), sub_zero]
  have hne : jqModC K - HahnSeries.C a ≠ 0 := by
    intro h; rw [h, HahnSeries.coeff_zero] at hcoeff; exact zero_ne_one hcoeff
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hcoeff]; exact one_ne_zero)) ?_
  by_contra hlt
  have hlt' : (jqModC K - HahnSeries.C a).order < -1 := lt_of_not_ge hlt
  have hne0 : (jqModC K - HahnSeries.C a).order ≠ 0 := by omega
  apply mt HahnSeries.coeff_order_eq_zero.mp hne
  rw [HahnSeries.coeff_sub, hC _ hne0, sub_zero]
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [ModularCurve.order_jqModC_def]
  exact hlt'

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R u) = HahnSeries.ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem theta_jqModC_int_mul_eisenstein4 :
    (HahnSeries.single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)) *
        HahnSeries.ofPowerSeries ℤ ℤ eisenstein4 =
      -(jqModC ℤ * HahnSeries.ofPowerSeries ℤ ℤ eisenstein6) := by
  apply coeffMap_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  rw [map_mul (coeffMap (Int.castRingHom ℚ)) (HahnSeries.single (1 : ℤ) (1 : ℤ) *
      LaurentSeries.derivative ℤ (jqModC ℤ)) (HahnSeries.ofPowerSeries ℤ ℤ eisenstein4),
    map_neg, map_mul (coeffMap (Int.castRingHom ℚ)) (jqModC ℤ) (HahnSeries.ofPowerSeries ℤ ℤ eisenstein6),
    coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, coeffMap_jqModC,
    ← ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC, jqModC_rat]
  exact ModularCurve.thetaL_jq_mul_eisenstein4_eq_neg_jq_mul_eisenstein6

theorem eisenstein4_map_of_charP_three [CharP K 3] : eisenstein4.map (Int.castRingHom K) = 1 := by
  ext n
  rw [PowerSeries.coeff_map, eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with h
  · exact map_one _
  · rw [map_mul, eq_intCast, show ((240 : ℤ) : K) = 0 from ?_, zero_mul]
    exact (CharP.intCast_eq_zero_iff K 3 240).mpr (by norm_num)

theorem eisenstein6_map_of_charP_three [CharP K 3] : eisenstein6.map (Int.castRingHom K) = 1 := by
  ext n
  rw [PowerSeries.coeff_map, eisenstein6, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with h
  · exact map_one _
  · rw [map_mul, eq_intCast, show ((-504 : ℤ) : K) = 0 from ?_, zero_mul]
    exact (CharP.intCast_eq_zero_iff K 3 (-504)).mpr (by norm_num)

theorem thetaJ_eq_neg_jqModC_of_charP_three [CharP K 3] : thetaJ K = -jqModC K := by
  have h := congrArg (coeffMap (Int.castRingHom K)) theta_jqModC_int_mul_eisenstein4
  rw [map_mul (coeffMap (Int.castRingHom K)) (HahnSeries.single (1 : ℤ) (1 : ℤ) *
      LaurentSeries.derivative ℤ (jqModC ℤ)) (HahnSeries.ofPowerSeries ℤ ℤ eisenstein4),
    map_neg, map_mul (coeffMap (Int.castRingHom K)) (jqModC ℤ) (HahnSeries.ofPowerSeries ℤ ℤ eisenstein6),
    coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, coeffMap_jqModC,
    ← ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC,
    eisenstein4_map_of_charP_three, eisenstein6_map_of_charP_three, map_one, mul_one, mul_one] at h
  exact h

end QSeries

section Hasse

variable (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]

theorem exists_hasse_exponents (hp5 : 5 ≤ p) :
    ∃ m e₄ e₆ : ℕ, 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have h2 : ¬ 2 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have h3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have hr : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  rcases hr with h | h | h | h
  · exact ⟨p / 12, 0, 0, by omega, by omega, by omega⟩
  · exact ⟨p / 12, 1, 0, by omega, by omega, by omega⟩
  · exact ⟨p / 12, 0, 1, by omega, by omega, by omega⟩
  · exact ⟨p / 12, 1, 1, by omega, by omega, by omega⟩

theorem order_prod {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has,
      HahnSeries.order_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem hasse_setup (hp5 : 5 ≤ p) :
    ∃ (m e₄ e₆ : ℕ) (S₀' : Finset K), 12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      (0 : K) ∉ S₀' ∧ (1728 : K) ∉ S₀' ∧ S₀'.card = m ∧
      thetaJ K ^ (p - 1) * (∏ a ∈ S₀', (jqModC K - HahnSeries.C a)) ^ 2 =
        jqModC K ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC K - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
  obtain ⟨m, e₄, e₆, hm, he₄, he₆⟩ := exists_hasse_exponents p hp5
  set S₀ : Finset K := (ModularCurve.ssJSet_finite p K).toFinset with hS₀
  have hS₀mem : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p K := fun a => by rw [hS₀, Set.Finite.mem_toFinset]
  have hid0 := ModularCurve.thetaL_jqModC_pow_mul_prod_sq_eq p hp5 m e₄ e₆ hm (by omega) he₆ K S₀ hS₀mem
  have hid : thetaJ K ^ (p - 1) * (∏ a ∈ S₀ \ {0, 1728}, (jqModC K - HahnSeries.C a)) ^ 2 =
      jqModC K ^ (8 * m + 2 * e₄ + 4 * e₆) * (jqModC K - 1728) ^ (6 * m + 2 * e₄ + 2 * e₆) := by
    simpa only [thetaJ] using hid0
  refine ⟨m, e₄, e₆, S₀ \ {0, 1728}, hm, he₄, he₆, by simp, by simp, ?_, ?_⟩
  ·
    have hprod0 : ∀ a ∈ S₀ \ {0, 1728}, jqModC K - HahnSeries.C a ≠ 0 := fun a _ h => by
      have := order_jqModC_sub_C K a; rw [h, HahnSeries.order_zero] at this; norm_num at this
    have hP0 : (∏ a ∈ S₀ \ {0, 1728}, (jqModC K - HahnSeries.C a)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hprod0
    have hj0 : jqModC K ≠ 0 := ModularCurve.jqModC_ne_zero_def K
    have hj1728 : jqModC K - 1728 ≠ 0 := by
      have := order_jqModC_sub_C K 1728
      rw [map_ofNat] at this
      intro h; rw [h, HahnSeries.order_zero] at this; norm_num at this
    have h := congrArg HahnSeries.order hid
    rw [HahnSeries.order_mul (pow_ne_zero _ (thetaJ_ne_zero K)) (pow_ne_zero _ hP0),
      HahnSeries.order_mul (pow_ne_zero _ hj0) (pow_ne_zero _ hj1728), HahnSeries.order_pow,
      HahnSeries.order_pow, HahnSeries.order_pow, HahnSeries.order_pow,
      order_thetaJ, ModularCurve.order_jqModC_def,
      order_prod K _ _ hprod0, Finset.sum_congr rfl (fun a _ => order_jqModC_sub_C K a),
      Finset.sum_const, show ((1728 : LaurentSeries K)) = HahnSeries.C (1728 : K) from (map_ofNat _ _).symm,
      order_jqModC_sub_C] at h
    simp only [nsmul_eq_mul, mul_neg, mul_one] at h
    have h' : ((p - 1 : ℕ) : ℤ) + 2 * ((S₀ \ {0, 1728}).card : ℤ) =
        ((8 * m + 2 * e₄ + 4 * e₆ : ℕ) : ℤ) + ((6 * m + 2 * e₄ + 2 * e₆ : ℕ) : ℤ) := by
      push_cast at h ⊢
      linarith
    have hp1 : ((p - 1 : ℕ) : ℤ) = 12 * m + 4 * e₄ + 6 * e₆ := by
      rw [← hm]; push_cast; ring
    rw [hp1] at h'
    push_cast at h'
    omega
  · exact hid

end Hasse

section IntLemmas

theorem intLemma_zero (p m e₄ e₆ e g g₂ : ℤ) (hp5 : 5 ≤ p) (hm : 12 * m + 4 * e₄ + 6 * e₆ = p - 1)
    (he₄ : 0 ≤ e₄) (he₄' : e₄ ≤ 1) (he : 0 < e) (hdvd : e ∣ 3)
    (h1 : 0 ≤ 6 * g + 4 * e) (hdag : g = p * g₂ + (8 * m + 2 * e₄ + 4 * e₆) * e) :
    0 ≤ 12 * g + (8 - 4 * e₄) * e := by
  rcases (show e₄ = 0 ∨ e₄ = 1 by omega) with rfl | rfl
  · nlinarith
  · have hle : e ≤ 3 := Int.le_of_dvd (by norm_num) hdvd
    have hcases : e = 1 ∨ e = 3 := by
      interval_cases e
      · exact Or.inl rfl
      · exfalso; norm_num at hdvd
      · exact Or.inr rfl
    rcases hcases with rfl | rfl
    · omega
    ·
      have hg : g = p * (g₂ + 2) - 4 := by rw [hdag]; nlinarith
      have hk : 1 ≤ g₂ + 2 := by
        by_contra hk
        have hk' : g₂ + 2 ≤ 0 := by omega
        nlinarith
      nlinarith

theorem intLemma_1728 (p m e₄ e₆ e g g₂ : ℤ) (hp5 : 5 ≤ p) (hm : 12 * m + 4 * e₄ + 6 * e₆ = p - 1)
    (he₆ : 0 ≤ e₆) (he₆' : e₆ ≤ 1) (he : 0 < e) (hdvd : e ∣ 2)
    (h1 : 0 ≤ 6 * g + 3 * e) (hdag : g = p * g₂ + (6 * m + 2 * e₄ + 2 * e₆) * e) :
    0 ≤ 12 * g + (6 - 6 * e₆) * e := by
  rcases (show e₆ = 0 ∨ e₆ = 1 by omega) with rfl | rfl
  · nlinarith
  · have hle : e ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
    have hcases : e = 1 ∨ e = 2 := by
      interval_cases e
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases with rfl | rfl
    · omega
    · have hg : g = p * (g₂ + 1) - 3 := by rw [hdag]; nlinarith
      have hk : 1 ≤ g₂ + 1 := by
        by_contra hk
        have hk' : g₂ + 1 ≤ 0 := by omega
        nlinarith
      nlinarith

theorem intLemma_ss (p g g₂ : ℤ) (hp3 : 3 ≤ p) (hg : 0 ≤ g) (hdag : g + 2 = p * g₂) : 1 ≤ g := by
  have hk : 1 ≤ g₂ := by
    by_contra hk
    have hk' : g₂ ≤ 0 := by omega
    nlinarith
  nlinarith

theorem intLemma_cusp (p m e₄ e₆ e g : ℤ) (hp5 : 5 ≤ p) (hm : 12 * m + 4 * e₄ + 6 * e₆ = p - 1)
    (he : 0 < e) (hg : e ≤ g) :
    0 < 12 * g + (8 - 4 * e₄) * (-e) + (6 - 6 * e₆) * (-e) - 12 * (m * (-e)) := by
  have h1 : (8 - 4 * e₄) * (-e) + (6 - 6 * e₆) * (-e) - 12 * (m * (-e)) = (p - 15) * e := by
    have : (12 * m + 4 * e₄ + 6 * e₆) * e = (p - 1) * e := by rw [hm]
    nlinarith
  have h2 : 0 ≤ (p - 5) * e := mul_nonneg (by omega) he.le
  nlinarith

theorem intLemma_three (e g t : ℤ) (he : 0 < e) (he6 : e ≤ 6) (h1 : 0 ≤ 6 * g + 7 * e)
    (ht : g + e = 3 * t) : 0 ≤ g + e := by
  omega

end IntLemmas

section MainFive

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N]
  (p : ℕ) [Fact p.Prime] [CharP K p]

theorem ofNat1728_ne_zero (hp5 : 5 ≤ p) : (1728 : K) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have h' : ((1728 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  have h2 : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at h' ⊢; exact h'
  rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h); omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h); omega

local notation "𝔧" => jj K N
local notation "𝔠" => algebraMap K (FN K N)

theorem coe_prod_sub (S₀' : Finset K) :
    ((∏ a ∈ S₀', (𝔧 - 𝔠 a) : FN K N) : LaurentSeries K) = ∏ a ∈ S₀', (jqModC K - HahnSeries.C a) := by
  have h := map_prod ((modularFunctionFieldC K N).val : FN K N →+* LaurentSeries K) (fun a => 𝔧 - 𝔠 a) S₀'
  refine h.trans (Finset.prod_congr rfl fun a _ => ?_)
  show ((𝔧 - 𝔠 a : FN K N) : LaurentSeries K) = _
  push_cast
  rw [LaurentSeries.algebraMap_apply]
  rfl

theorem main_ge_five (hp5 : 5 ≤ p) (hpN : ¬ p ∣ N) (G G₂ : FN K N)
    (hG : IsModPFormFn K 1 (G : LaurentSeries K))
    (hpow : qexpOfWeight K 1 (G : LaurentSeries K) = qexpOfWeight K 1 (G₂ : LaurentSeries K) ^ p) :
    G = 0 := by
  have hp : p.Prime := Fact.out
  by_contra hG0
  obtain ⟨m, e₄, e₆, S₀', hm, he₄, he₆, h0S, h1728S, hcard, hH⟩ := hasse_setup K p hp5
  set a2 : ℕ := 8 * m + 2 * e₄ + 4 * e₆ with ha2
  set b2 : ℕ := 6 * m + 2 * e₄ + 2 * e₆ with hb2
  set α : ℕ := 8 - 4 * e₄ with hα
  set β : ℕ := 6 - 6 * e₆ with hβ
  have hαZ : (α : ℤ) = 8 - 4 * e₄ := by omega
  have hβZ : (β : ℤ) = 6 - 6 * e₆ := by omega
  have hmZ : (12 * m + 4 * e₄ + 6 * e₆ : ℤ) = p - 1 := by omega
  have hp5Z : (5 : ℤ) ≤ p := by exact_mod_cast hp5
  set Sj : FN K N := ∏ a ∈ S₀', (𝔧 - 𝔠 a) with hSj
  have h1728K : (1728 : K) ≠ 0 := ofNat1728_ne_zero p hp5
  have hj0 : (𝔧 : FN K N) ≠ 0 := jj_ne_zero K N
  have hja : ∀ a : K, (𝔧 - 𝔠 a : FN K N) ≠ 0 := fun a => jGeomGen_sub_algebraMap_ne_zero K N a
  have hSj0 : Sj ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hja a

  have hdag : G * Sj ^ 2 = G₂ ^ p * 𝔧 ^ a2 * (𝔧 - 𝔠 1728) ^ b2 := by
    apply Subtype.val_injective
    have hT : thetaJ K ≠ 0 := thetaJ_ne_zero K
    have hpow' : (G : LaurentSeries K) = (G₂ : LaurentSeries K) ^ p * thetaJ K ^ (p - 1) := by
      have h1 : (G : LaurentSeries K) * thetaJ K =
          ((G₂ : LaurentSeries K) ^ p * thetaJ K ^ (p - 1)) * thetaJ K := by
        rw [qexpOfWeight, qexpOfWeight, zpow_one, mul_pow] at hpow
        rw [hpow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.one_le]
      exact mul_right_cancel₀ hT h1
    show ((G * Sj ^ 2 : FN K N) : LaurentSeries K) =
      ((G₂ ^ p * 𝔧 ^ a2 * (𝔧 - 𝔠 1728) ^ b2 : FN K N) : LaurentSeries K)
    push_cast
    rw [hSj, coe_prod_sub, hpow', LaurentSeries.algebraMap_apply, map_ofNat, mul_assoc, hH, mul_assoc]
    rfl
  have hG₂0 : G₂ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero, zero_mul, zero_mul, mul_eq_zero] at hdag
    rcases hdag with h | h
    · exact hG0 h
    · exact hSj0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)

  set Z : FN K N := G ^ 12 * 𝔧 ^ α * (𝔧 - 𝔠 1728) ^ β / Sj ^ 12 with hZ
  have hZ0 : Z ≠ 0 := by
    rw [hZ]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0))
      (pow_ne_zero _ (hja 1728))) (pow_ne_zero _ hSj0)

  have hordZ : ∀ v : Place K (FN K N), v.ord Z =
      12 * v.ord G + (α : ℤ) * v.ord 𝔧 + (β : ℤ) * v.ord (𝔧 - 𝔠 1728) - 12 * v.ord Sj := by
    intro v
    rw [hZ, div_eq_mul_inv,
      v.ord_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0))
        (pow_ne_zero _ (hja 1728))) (inv_ne_zero (pow_ne_zero _ hSj0)),
      v.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ (hja 1728)),
      v.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), v.ord_inv, ord_pow, ord_pow, ord_pow, ord_pow]
    push_cast
    ring
  have horddag : ∀ v : Place K (FN K N), v.ord G + 2 * v.ord Sj =
      (p : ℤ) * v.ord G₂ + (a2 : ℤ) * v.ord 𝔧 + (b2 : ℤ) * v.ord (𝔧 - 𝔠 1728) := by
    intro v
    have h := congrArg v.ord hdag
    rw [v.ord_mul hG0 (pow_ne_zero _ hSj0), ord_pow,
      v.ord_mul (mul_ne_zero (pow_ne_zero _ hG₂0) (pow_ne_zero _ hj0)) (pow_ne_zero _ (hja 1728)),
      v.ord_mul (pow_ne_zero _ hG₂0) (pow_ne_zero _ hj0), ord_pow, ord_pow, ord_pow] at h
    push_cast at h
    linarith
  have hordSj : ∀ v : Place K (FN K N), v.ord Sj = ∑ a ∈ S₀', v.ord (𝔧 - 𝔠 a) := fun v =>
    ord_prod v S₀' _ fun a _ => hja a

  have hint1 : ∀ v : Place K (FN K N), (𝔧 : FN K N) ∈ v.toValuationSubring →
      0 ≤ 6 * v.ord G + 4 * v.ord 𝔧 + 3 * v.ord (𝔧 - 𝔠 1728) := by
    intro v hv
    have h := ord_nonneg_of_mem v (mem_of_isModPFormFn_of_jj_mem hG hv)
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0)) (pow_ne_zero _ (hja 1728)),
      v.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0), ord_pow, ord_pow, ord_pow] at h
    push_cast at h
    linarith
  have hint2 : ∀ v : Place K (FN K N), (𝔧 : FN K N)⁻¹ ∈ v.toValuationSubring →
      0 ≤ 2 * v.ord G + v.ord 𝔧 + v.ord (𝔧 - 𝔠 1728) := by
    intro v hv
    have h := ord_nonneg_of_mem v (mem_of_isModPFormFn_of_inv_jj_mem hG hv)
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) hj0) (hja 1728),
      v.ord_mul (pow_ne_zero _ hG0) hj0, ord_pow] at h
    push_cast at h
    linarith

  have hj_sub_zero : (𝔧 - 𝔠 0 : FN K N) = 𝔧 := by rw [map_zero, sub_zero]

  have hmain : ∀ v : Place K (FN K N), 0 ≤ v.ord Z ∧ (v.ord 𝔧 < 0 → 0 < v.ord Z) := by
    intro v
    rcases place_cases v with ⟨hneg, hall⟩ | ⟨hmem, j₀, hpos, hother⟩
    ·
      have hos : v.ord Sj = (m : ℤ) * v.ord 𝔧 := by
        rw [hordSj, Finset.sum_congr rfl (fun a _ => hall a), Finset.sum_const, hcard, nsmul_eq_mul]
      have h2 := hint2 v (inv_jj_mem_of_ord_neg hneg)
      rw [hall 1728] at h2
      set e : ℤ := -v.ord 𝔧 with he
      have hoj : v.ord 𝔧 = -e := by omega
      have hpos : 0 < v.ord Z := by
        rw [hordZ, hall 1728, hos, hoj, hαZ, hβZ]
        exact intLemma_cusp p m e₄ e₆ e (v.ord G) hp5Z hmZ (by omega) (by omega)
      exact ⟨hpos.le, fun _ => hpos⟩
    ·
      have hojnn : 0 ≤ v.ord 𝔧 := ord_nonneg_of_mem v hmem
      refine ⟨?_, fun h => absurd h (not_lt.mpr hojnn)⟩
      obtain ⟨d, hd, hdvd⟩ := ord_sub_dvd_jWidth p hp5 hpN v j₀ hpos
      have h1 := hint1 v hmem
      have hdagv := horddag v
      by_cases hj₀0 : j₀ = 0
      ·
        subst hj₀0
        rw [hj_sub_zero] at hpos hd
        have ho' : v.ord (𝔧 - 𝔠 1728) = 0 := hother 1728 h1728K
        have hos : v.ord Sj = 0 := by
          rw [hordSj]
          exact Finset.sum_eq_zero fun a ha => hother a (fun h => h0S (h ▸ ha))
        rw [ModularCurve.jWidth_of_eq_zero rfl] at hdvd
        rw [ho'] at h1
        rw [ho', hos] at hdagv
        rw [hordZ, ho', hos, hαZ]
        have := intLemma_zero p m e₄ e₆ (v.ord 𝔧) (v.ord G) (v.ord G₂) hp5Z
          hmZ (by omega) (by exact_mod_cast he₄) hpos
          (by rw [hd]; exact_mod_cast hdvd) (by linarith) (by rw [ha2] at hdagv; push_cast at hdagv; linarith)
        linarith
      by_cases hj₀1728 : j₀ = 1728
      ·
        subst hj₀1728
        have hoj : v.ord 𝔧 = 0 := by rw [← hj_sub_zero]; exact hother 0 h1728K.symm
        have hos : v.ord Sj = 0 := by
          rw [hordSj]
          exact Finset.sum_eq_zero fun a ha => hother a (fun h => h1728S (h ▸ ha))
        rw [ModularCurve.jWidth_of_eq_1728 rfl h1728K] at hdvd
        rw [hoj] at h1
        rw [hoj, hos] at hdagv
        rw [hordZ, hoj, hos, hβZ]
        have := intLemma_1728 p m e₄ e₆ (v.ord (𝔧 - 𝔠 1728)) (v.ord G) (v.ord G₂)
          hp5Z hmZ (by omega) (by exact_mod_cast he₆) hpos
          (by rw [hd]; exact_mod_cast hdvd) (by linarith) (by rw [hb2] at hdagv; push_cast at hdagv; linarith)
        linarith

      have hoj : v.ord 𝔧 = 0 := by rw [← hj_sub_zero]; exact hother 0 (Ne.symm hj₀0)
      have ho' : v.ord (𝔧 - 𝔠 1728) = 0 := hother 1728 (Ne.symm hj₀1728)
      rw [hoj, ho'] at hdagv h1
      by_cases hss : j₀ ∈ S₀'
      ·
        have hos : v.ord Sj = v.ord (𝔧 - 𝔠 j₀) := by
          rw [hordSj]
          exact Finset.sum_eq_single_of_mem j₀ hss fun a _ ha => hother a ha
        rw [ModularCurve.jWidth_of_ne hj₀0 hj₀1728, Nat.dvd_one] at hdvd
        rw [hdvd, Nat.cast_one] at hd
        rw [hos, hd] at hdagv
        rw [hordZ, hoj, ho', hos, hd]
        have := intLemma_ss p (v.ord G) (v.ord G₂) (by exact_mod_cast (by omega : 3 ≤ p)) (by linarith)
          (by linarith)
        linarith
      ·
        have hos : v.ord Sj = 0 := by
          rw [hordSj]
          exact Finset.sum_eq_zero fun a ha => hother a (fun h => hss (h ▸ ha))
        rw [hordZ, hoj, ho', hos]
        linarith

  have hcusp : 0 < (cuspInftyGeom K N).ord Z :=
    (hmain _).2 (by rw [ord_cusp_jj]; norm_num)
  exact hZ0 (eq_zero_of_forall_ord_nonneg_of_ord_pos (cuspInftyGeom K N) (deg_cusp_ne_zero K N)
    (fun w => (hmain w).1) hcusp)

end MainFive

section MainThree

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] {N : ℕ} [NeZero N] [CharP K 3]

local notation "𝔧" => jj K N
local notation "𝔠" => algebraMap K (FN K N)

theorem main_three (h3N : ¬ 3 ∣ N) (G G₂ : FN K N)
    (hG : IsModPFormFn K 1 (G : LaurentSeries K))
    (hpow : qexpOfWeight K 1 (G : LaurentSeries K) = qexpOfWeight K 1 (G₂ : LaurentSeries K) ^ 3)
    (hcusp : (qexpOfWeight K 1 (G : LaurentSeries K)).coeff 0 = 0) :
    G = 0 := by
  by_contra hG0
  have hθ : thetaJ K = -jqModC K := thetaJ_eq_neg_jqModC_of_charP_three K
  have h1728K : (1728 : K) = 0 := by
    have : ((1728 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 3 1728).mpr (by norm_num)
    exact_mod_cast this
  have hc1728 : (𝔠 1728 : FN K N) = 0 := by rw [h1728K, map_zero]
  have hj0 : (𝔧 : FN K N) ≠ 0 := jj_ne_zero K N

  have hH : G * 𝔧 = (G₂ * 𝔧) ^ 3 := by
    apply Subtype.val_injective
    have h := hpow
    rw [qexpOfWeight, qexpOfWeight, zpow_one, hθ, mul_pow] at h
    have h' : (G : LaurentSeries K) * jqModC K = (G₂ : LaurentSeries K) ^ 3 * jqModC K ^ 3 := by
      have h3 : (-jqModC K) ^ 3 = -(jqModC K ^ 3) := by ring
      rw [h3, mul_neg, mul_neg, neg_inj] at h
      exact h
    show ((G * 𝔧 : FN K N) : LaurentSeries K) = (((G₂ * 𝔧) ^ 3 : FN K N) : LaurentSeries K)
    push_cast
    rw [mul_pow]
    exact h'
  set H : FN K N := G * 𝔧 with hHdef
  have hH0 : H ≠ 0 := mul_ne_zero hG0 hj0
  have hj_sub_zero : (𝔧 - 𝔠 0 : FN K N) = 𝔧 := by rw [map_zero, sub_zero]

  have hmain : ∀ v : Place K (FN K N), 0 ≤ v.ord H := by
    intro v
    rcases place_cases v with ⟨hneg, hall⟩ | ⟨hmem, j₀, hpos, hother⟩
    ·
      have h := ord_nonneg_of_mem v (mem_of_isModPFormFn_of_inv_jj_mem hG (inv_jj_mem_of_ord_neg hneg))
      rw [hc1728, sub_zero, v.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) hj0) hj0,
        v.ord_mul (pow_ne_zero _ hG0) hj0, ord_pow] at h
      rw [hHdef, v.ord_mul hG0 hj0]
      push_cast at h
      linarith
    · have h1 := ord_nonneg_of_mem v (mem_of_isModPFormFn_of_jj_mem hG hmem)
      rw [hc1728, sub_zero, v.ord_mul (mul_ne_zero (pow_ne_zero _ hG0) (pow_ne_zero _ hj0))
        (pow_ne_zero _ hj0), v.ord_mul (pow_ne_zero _ hG0) (pow_ne_zero _ hj0),
        ord_pow, ord_pow, ord_pow] at h1
      push_cast at h1
      rw [hHdef, v.ord_mul hG0 hj0]
      by_cases hj₀0 : j₀ = 0
      ·
        subst hj₀0
        rw [hj_sub_zero] at hpos
        have hle : v.ord 𝔧 ≤ 6 := ord_jj_le_six h3N v hpos
        have hG₂0 : G₂ ≠ 0 := by
          intro h; rw [h, zero_mul, zero_pow three_ne_zero] at hH; exact hH0 hH
        have h3 : v.ord G + v.ord 𝔧 = 3 * v.ord (G₂ * 𝔧) := by
          have := congrArg v.ord hH
          rw [v.ord_mul hG0 hj0, ord_pow] at this
          exact_mod_cast this
        exact intLemma_three (v.ord 𝔧) (v.ord G) (v.ord (G₂ * 𝔧)) hpos hle (by linarith) h3
      · have hoj : v.ord 𝔧 = 0 := by rw [← hj_sub_zero]; exact hother 0 (Ne.symm hj₀0)
        rw [hoj] at h1 ⊢
        linarith

  have hcoeH : ((H : FN K N) : LaurentSeries K) = -qexpOfWeight K 1 (G : LaurentSeries K) := by
    rw [qexpOfWeight, zpow_one, hθ, mul_neg, neg_neg, hHdef]
    push_cast
    rfl
  have hcuspord : 0 < (cuspInftyGeom K N).ord H := by
    have hnn : 0 ≤ ((H : FN K N) : LaurentSeries K).order := by rw [← ord_cusp]; exact hmain _
    rw [ord_cusp]
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hne : ((H : FN K N) : LaurentSeries K) ≠ 0 := by
        intro h0; exact hH0 (Subtype.val_injective (by rw [h0]; rfl))
      have hc := mt HahnSeries.coeff_order_eq_zero.mp hne
      rw [← h, hcoeH, HahnSeries.coeff_neg, hcusp, neg_zero] at hc
      exact hc rfl
  exact hH0 (eq_zero_of_forall_ord_nonneg_of_ord_pos (cuspInftyGeom K N) (deg_cusp_ne_zero K N)
    hmain hcuspord)

end MainThree

end KATZ2C
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow.KATZ2C"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (G G₂ : ↥(modularFunctionFieldC K N))
    (hG : IsModPFormFn K 1 (G : LaurentSeries K))
    (hpow : qexpOfWeight K 1 (G : LaurentSeries K) =
      qexpOfWeight K 1 (G₂ : LaurentSeries K) ^ p)
    (hcusp : (qexpOfWeight K 1 (G : LaurentSeries K)).coeff 0 = 0) :
    G = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
  have hcases : p = 3 ∨ 5 ≤ p := by have := hp.two_le; omega
  rcases hcases with rfl | hp5
  · exact KATZ2C.main_three hpN G G₂ hG hpow hcusp
  · exact KATZ2C.main_ge_five p hp5 hpN G G₂ hG hpow

end
p2m_reactivate "P2MW.S_ModularCurve_eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow.KATZ2C"

end S_ModularCurve_eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_isModPFormFn_one_of_qexpOfWeight_eq_pow (solution)
