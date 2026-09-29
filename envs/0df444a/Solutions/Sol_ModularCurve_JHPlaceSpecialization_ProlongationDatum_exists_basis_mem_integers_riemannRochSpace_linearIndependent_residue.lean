-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2d76bf64-df8d-5a9e-902e-4a549a71bee6

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta"
p2m_attr_erase "simp" "ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

namespace DefectH

section InsepDegree
variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]

theorem InsepH.not_mem_adjoin_pow_of_transcendental {q : ℕ} (hq : q.Prime) {t : F}
    (ht : Transcendental κ t) : t ∉ IntermediateField.adjoin κ ({t ^ q} : Set F) := by
  intro hmem
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff κ t).mp hmem
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hrs
    rw [hrs] at ht
    exact ht isAlgebraic_zero
  have hS : Polynomial.aeval (t ^ q) s ≠ 0 := fun h0 =>
    hs0 ((Polynomial.expand_eq_zero hq.pos).mp
      (transcendental_iff.mp ht (Polynomial.expand κ q s) (by rwa [Polynomial.expand_aeval])))
  have hmul : t * Polynomial.aeval (t ^ q) s = Polynomial.aeval (t ^ q) r := (eq_div_iff hS).mp hrs
  have hP : Polynomial.aeval t (Polynomial.X * Polynomial.expand κ q s - Polynomial.expand κ q r) = 0 := by
    rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.expand_aeval, Polynomial.expand_aeval, hmul,
      sub_self]
  have hz := transcendental_iff.mp ht _ hP
  have hnd : ¬ q ∣ q * s.natDegree + 1 := fun h =>
    hq.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right q _)).mp h))
  have hc := congrArg (fun p : Polynomial κ => p.coeff (q * s.natDegree + 1)) hz
  simp only [Polynomial.coeff_sub, Polynomial.coeff_zero, Polynomial.coeff_X_mul,
    Polynomial.coeff_expand hq.pos] at hc
  rw [if_pos (dvd_mul_right q _), if_neg hnd, Nat.mul_div_cancel_left _ hq.pos, sub_zero,
    Polynomial.coeff_natDegree] at hc
  exact hs0 (Polynomial.leadingCoeff_eq_zero.mp hc)

theorem InsepH.relfinrank_adjoin_pow_char (q : ℕ) (hq : q.Prime) [CharP κ q] {t : F}
    (ht : Transcendental κ t) :
    (IntermediateField.adjoin κ ({t ^ q} : Set F)).relfinrank (IntermediateField.adjoin κ ({t} : Set F))
      = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP F q := charP_of_injective_algebraMap (algebraMap κ F).injective q
  have hle : IntermediateField.adjoin κ ({t ^ q} : Set F) ≤ IntermediateField.adjoin κ ({t} : Set F) :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self κ t) q)
  have hnot := InsepH.not_mem_adjoin_pow_of_transcendental (κ := κ) hq ht
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]

  have hE : IntermediateField.extendScalars hle
      = IntermediateField.adjoin (IntermediateField.adjoin κ ({t ^ q} : Set F)) ({t} : Set F) := by
    apply le_antisymm
    · intro x hx
      have hsub : IntermediateField.adjoin κ ({t} : Set F) ≤
          (IntermediateField.adjoin (IntermediateField.adjoin κ ({t ^ q} : Set F))
            ({t} : Set F)).restrictScalars κ :=
        IntermediateField.adjoin_simple_le_iff.mpr
          (IntermediateField.mem_adjoin_simple_self (IntermediateField.adjoin κ ({t ^ q} : Set F)) t)
      exact hsub ((IntermediateField.mem_extendScalars hle).mp hx)
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_extendScalars hle).mpr (IntermediateField.mem_adjoin_simple_self κ t))
  rw [hE]

  obtain ⟨a, ha⟩ : ∃ a : IntermediateField.adjoin κ ({t ^ q} : Set F), (a : F) = t ^ q :=
    ⟨⟨t ^ q, IntermediateField.mem_adjoin_simple_self κ (t ^ q)⟩, rfl⟩
  have hmonic : (Polynomial.X ^ q - Polynomial.C a).Monic := Polynomial.monic_X_pow_sub_C a hq.ne_zero
  have haeval : Polynomial.aeval t (Polynomial.X ^ q - Polynomial.C a) = 0 := by simp [ha]
  have hirr : Irreducible (Polynomial.X ^ q - Polynomial.C a) := by
    refine X_pow_sub_C_irreducible_of_prime hq fun b hb => hnot ?_
    have h1 : (b : F) ^ q = t ^ q := by
      have h := congrArg (fun x : IntermediateField.adjoin κ ({t ^ q} : Set F) => (x : F)) hb
      simpa [ha] using h
    have h3 : ((b : F) - t) ^ q = 0 := by rw [sub_pow_char, h1, sub_self]
    have h2 : (b : F) = t := sub_eq_zero.mp ((pow_eq_zero_iff hq.ne_zero).mp h3)
    have hb2 : (b : F) ∈ IntermediateField.adjoin κ ({t ^ q} : Set F) := b.2
    rw [h2] at hb2
    exact hb2
  have hint : IsIntegral (IntermediateField.adjoin κ ({t ^ q} : Set F)) t :=
    ⟨_, hmonic, by rwa [← Polynomial.aeval_def]⟩
  have hmin := minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_X_pow_sub_C]

theorem InsepH.finrank_adjoin_pow_char (q : ℕ) (hq : q.Prime) [CharP κ q] {t : F}
    (ht : Transcendental κ t) :
    Module.finrank (IntermediateField.adjoin κ ({t ^ q} : Set F)) F
      = q * Module.finrank (IntermediateField.adjoin κ ({t} : Set F)) F := by
  have hle : IntermediateField.adjoin κ ({t ^ q} : Set F) ≤ IntermediateField.adjoin κ ({t} : Set F) :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self κ t) q)
  rw [← IntermediateField.relfinrank_mul_finrank_top hle, InsepH.relfinrank_adjoin_pow_char q hq ht]

end InsepDegree

section Tower
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finrank_adjoin_map_eq_mul (φ : F →ₐ[K] F') (x : F) :
    Module.finrank ↥(IntermediateField.adjoin K ({φ x} : Set F')) F'
      = Module.finrank ↥(IntermediateField.adjoin K ({x} : Set F)) F * finrankAlong K φ := by
  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  let Kx := IntermediateField.adjoin K ({x} : Set F)
  letI : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have htower : Module.finrank Kx F * Module.finrank F F' = Module.finrank Kx F' :=
    Module.finrank_mul_finrank Kx F F'
  have hfa : finrankAlong K φ = Module.finrank F F' := rfl
  rw [hfa, htower]

  have hmap : (IntermediateField.adjoin K ({x} : Set F)).map φ = IntermediateField.adjoin K ({φ x} : Set F') := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
  let e : Kx ≃ₐ[K] ↥(IntermediateField.adjoin K ({φ x} : Set F')) :=
    (IntermediateField.equivMap Kx φ).trans (IntermediateField.equivOfEq hmap)
  symm
  refine Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext a
  show ((e a : ↥(IntermediateField.adjoin K ({φ x} : Set F'))) : F') = φ (a : F)
  first
    | rfl
    | (simp only [e, AlgEquiv.trans_apply]; rfl)
    | (simp [e, IntermediateField.equivMap, IntermediateField.equivOfEq])

end Tower

theorem finrank_adjoin_congr {K E : Type*} [Field K] [Field E] [Algebra K E] {S T : IntermediateField K E}
    (h : S = T) (x : S) :
    Module.finrank ↥(IntermediateField.adjoin K ({x} : Set S)) S
      = Module.finrank ↥(IntermediateField.adjoin K ({(⟨(x : E), h ▸ x.2⟩ : T)} : Set T)) T := by
  subst h
  rfl

end DefectH

namespace DefectH

section AlongEquiv
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem finrankAlong_eq_one_of_bijective (φ : F →ₐ[K] F') (hφ : Function.Bijective φ) : finrankAlong K φ = 1 := by
  letI : Algebra F F' := algebraAlong φ
  have hb : Function.Bijective (Algebra.ofId F F') := hφ
  show Module.finrank F F' = 1
  rw [← (AlgEquiv.ofBijective (Algebra.ofId F F') hb).toLinearEquiv.finrank_eq, Module.finrank_self]

end AlongEquiv

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem integers_ne_integers
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (xj : ↥(xHFunctionFieldBar M H)) (h₁ : xj ∈ Rpd.R₁.integers) (h₂ : xj ∈ Rpd.R₂.integers)
    (jb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hjb : ((jb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hr₁ : Rpd.R₁.residue ⟨xj, h₁⟩ = jb) (hr₂ : Rpd.R₂.residue ⟨xj, h₂⟩ = jb ^ p)
    (htr : Transcendental (ResidueField ↥A) jb) :
    Rpd.R₁.integers ≠ Rpd.R₂.integers := by
  classical
  have hp : p.Prime := Fact.out
  intro heq

  have hθO : ∀ f, f ∈ Rpd.R₁.integers → θ f ∈ Rpd.R₁.integers := fun f hf =>
    (Rpd.mem_integers₂_iff f).mp (heq ▸ hf)
  have hθO' : ∀ f, f ∈ Rpd.R₁.integers → θ.symm f ∈ Rpd.R₁.integers := fun f hf => by
    have h : θ.symm f ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff (θ.symm f)).mpr (by rw [AlgEquiv.apply_symm_apply]; exact hf)
    rwa [← heq] at h

  let ρ : Rpd.R₁.integers →+* (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    { toFun := fun a => Rpd.R₁.residue ⟨θ a, hθO a a.2⟩
      map_one' := by
        have e : (⟨θ (1 : Rpd.R₁.integers), hθO _ (1 : Rpd.R₁.integers).2⟩ : Rpd.R₁.integers) = 1 := Subtype.ext (by simp)
        rw [e, map_one]
      map_mul' := fun a b => by
        have e : (⟨θ ((a * b : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)), hθO _ (a * b).2⟩ : Rpd.R₁.integers)
            = ⟨θ a, hθO a a.2⟩ * ⟨θ b, hθO b b.2⟩ := Subtype.ext (by simp)
        rw [e, map_mul]
      map_zero' := by
        have e : (⟨θ (0 : Rpd.R₁.integers), hθO _ (0 : Rpd.R₁.integers).2⟩ : Rpd.R₁.integers) = 0 := Subtype.ext (by simp)
        rw [e, map_zero]
      map_add' := fun a b => by
        have e : (⟨θ ((a + b : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)), hθO _ (a + b).2⟩ : Rpd.R₁.integers)
            = ⟨θ a, hθO a a.2⟩ + ⟨θ b, hθO b b.2⟩ := Subtype.ext (by simp)
        rw [e, map_add] }
  have hρ : ∀ a : Rpd.R₁.integers, ρ a = Rpd.R₁.residue ⟨θ a, hθO a a.2⟩ := fun a => rfl

  have hker : RingHom.ker Rpd.R₁.residue ≤ RingHom.ker ρ := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [hρ]
    by_contra hne
    have hu : IsUnit (⟨θ a, hθO a a.2⟩ : Rpd.R₁.integers) := Rpd.R₁.isUnit_of_residue_ne_zero hne
    apply Rpd.R₁.residue_ne_zero_of_isUnit _ ha

    obtain ⟨u, hu'⟩ := hu
    have hinvmem : ((↑u⁻¹ : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers := (↑u⁻¹ : Rpd.R₁.integers).2
    have hprod : (θ a) * ((↑u⁻¹ : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)) = 1 := by
      have h := congrArg (fun z : Rpd.R₁.integers => (z : ↥(xHFunctionFieldBar M H))) (u.mul_inv)
      simp only [hu'] at h
      exact h
    refine isUnit_iff_exists_inv.mpr ⟨⟨θ.symm ((↑u⁻¹ : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)), hθO' _ hinvmem⟩, Subtype.ext ?_⟩
    show (a : ↥(xHFunctionFieldBar M H)) * θ.symm ((↑u⁻¹ : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)) = 1
    apply θ.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, map_one]
    exact hprod

  let σ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →+* (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    RingHom.liftOfRightInverse Rpd.R₁.residue (Function.surjInv Rpd.R₁.residue_surjective)
      (Function.rightInverse_surjInv Rpd.R₁.residue_surjective) ⟨ρ, hker⟩
  have hσ : ∀ a : Rpd.R₁.integers, σ (Rpd.R₁.residue a) = ρ a := fun a =>
    RingHom.liftOfRightInverse_comp_apply Rpd.R₁.residue _ _ ⟨ρ, hker⟩ a

  have hσκ : ∀ c : (ResidueField ↥A), σ (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c) = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    have hmem : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) ∈ Rpd.R₁.integers := (Rpd.R₁.algebraMap_mem_iff _).mpr a.2
    rw [← Rpd.R₁.residue_algebraMap a, hσ, hρ]
    have e : (⟨θ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))), hθO _ hmem⟩ : Rpd.R₁.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)), hmem⟩ := Subtype.ext (by simp)
    rw [e, Rpd.R₁.residue_algebraMap a]
  let σ' : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →ₐ[(ResidueField ↥A)] (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := { σ with commutes' := hσκ }

  have hσsurj : Function.Surjective σ' := by
    intro b
    obtain ⟨a, rfl⟩ := Rpd.R₁.residue_surjective b
    refine ⟨Rpd.R₁.residue ⟨θ.symm a, hθO' a a.2⟩, ?_⟩
    show σ (Rpd.R₁.residue ⟨θ.symm a, hθO' a a.2⟩) = Rpd.R₁.residue a
    rw [hσ, hρ]
    congr 1
    exact Subtype.ext (by simp)
  have hσbij : Function.Bijective σ' := ⟨σ'.toRingHom.injective, hσsurj⟩

  have hσjb : σ' jb = jb ^ p := by
    show σ jb = jb ^ p
    rw [← hr₂, Rpd.residue₂_eq xj h₂, ← hr₁, hσ, hρ]

  have hins := InsepH.finrank_adjoin_pow_char (κ := (ResidueField ↥A)) (F := (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) p hp htr
  have halong := finrank_adjoin_map_eq_mul σ' jb
  rw [finrankAlong_eq_one_of_bijective σ' hσbij, mul_one, hσjb, hins] at halong

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    rw [hM, hc]; ring
  have hN0 : ((M / p : ℕ) : (ResidueField ↥A)) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff (ResidueField ↥A) p (M / p)).mp h0)
  have hd₁ := finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 (ResidueField ↥A) (M / p) hN0
    (JHNeronObjectAtP.ΓN p M H hpM) (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
    (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) jb hjb
  haveI : (JHNeronObjectAtP.ΓN p M H hpM ⊔ Subgroup.zpowers (-1)).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  have hpos : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({jb} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := by
    rw [hd₁]
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : p = 1 := Nat.eq_of_mul_eq_mul_right hpos (halong.trans (one_mul _).symm)
  exact hp.ne_one this

theorem heq_core
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (h₁ : α x ∈ Rpd.R₁.integers) (h₂ : α x ∈ Rpd.R₂.integers)
    (hr₂pow : Rpd.R₂.residue ⟨α x, h₂⟩ = (Rpd.R₁.residue ⟨α x, h₁⟩) ^ p) :
    Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({Rpd.R₁.residue ⟨α x, h₁⟩} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) +
      Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({Rpd.R₂.residue ⟨α x, h₂⟩} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) =
      Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({α x} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    rw [hM, hc]; ring

  have hxj_coe : ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hα_coe, hx]
  have hr₁_coe : ((Rpd.R₁.residue ⟨α x, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have hval : coeffMap A.subtype (jqModC ↥A) = ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hxj_coe]
      exact map_jqModC A.subtype
    have hy : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
      rw [hval]
      exact (α x).2
    obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hy
    have e : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(xHFunctionFieldBar M H)) = α x := Subtype.ext hval
    have e' : (⟨α x, h₁⟩ : Rpd.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
    rw [e', hres]
    exact map_jqModC (IsLocalRing.residue ↥A)
  have hr₂ := hr₂pow

  have htr : Transcendental (ResidueField ↥A) (Rpd.R₁.residue ⟨α x, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible (ResidueField ↥A) (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp ((minpoly.degree_eq_one_iff (A := (ResidueField ↥A))
      (x := (Rpd.R₁.residue ⟨α x, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))).mp hdeg)
    have h0 : algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c = jqModC (ResidueField ↥A) := by
      rw [← hr₁_coe]; exact congrArg Subtype.val hc
    rw [algebraMap_laurentSeries_eq_single] at h0
    have hc2 := congrArg (fun s : LaurentSeries (ResidueField ↥A) => s.coeff (-1 : ℤ)) h0
    change (HahnSeries.single (0 : ℤ) c).coeff (-1 : ℤ) = (jqModC (ResidueField ↥A)).coeff (-1 : ℤ) at hc2
    rw [HahnSeries.coeff_single_of_ne (by decide : (-1 : ℤ) ≠ 0), coeff_jqModC_neg_one] at hc2
    exact zero_ne_one hc2

  have hd₂ := InsepH.finrank_adjoin_pow_char (κ := (ResidueField ↥A)) (F := (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) p hp htr
  have hN0 : ((M / p : ℕ) : (ResidueField ↥A)) ≠ 0 := fun h0 => hpN ((CharP.cast_eq_zero_iff (ResidueField ↥A) p (M / p)).mp h0)
  have hd₁ := finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 (ResidueField ↥A) (M / p) hN0
    (JHNeronObjectAtP.ΓN p M H hpM) (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
    (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) (Rpd.R₁.residue ⟨α x, h₁⟩) hr₁_coe

  have hup := DefectH.finrank_adjoin_map_eq_mul α x
  have hfa := finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe
  have hbc : laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM))
      = qExpFunctionFieldC (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM) :=
    laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) (JHNeronObjectAtP.ΓN p M H hpM)
  have hN0' : ((M / p : ℕ) : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (M / p))
  have hdn : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
      = (JHNeronObjectAtP.ΓN p M H hpM ⊔ Subgroup.zpowers (-1)).index := by
    refine (finrank_adjoin_congr hbc x).trans ?_
    exact finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 (AlgebraicClosure ℚ) (M / p) hN0'
      (JHNeronObjectAtP.ΓN p M H hpM) (Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
      (CohCarrier.GammaH_le_Gamma0 (infSubgroup p M H hpM)) _ hx

  rw [hr₂, hd₂, hd₁, hup, hfa, hdn]
  ring

end DefectH

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ (u : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(xHFunctionFieldBar M H))
      (hu₁ : ∀ a, u a ∈ Rpd.R₁.integers) (hu₂ : ∀ a, u a ∈ Rpd.R₂.integers),
      (∀ a, u a ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField ↥A) (fun a => ((Rpd.R₁.residue ⟨u a, hu₁ a⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (Rpd.R₂.residue ⟨u a, hu₂ a⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) := by
  clear hTD hFix hmodel hO hRL hNV hθgal hSS hδ hpb
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hxj : ∃ uj : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((uj : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    have hmem : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
      intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)
    refine ⟨⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩, ?_⟩
    exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  obtain ⟨uj, huj⟩ := hxj
  let xj : ↥(xHFunctionFieldBar M H) := α uj
  have hxj_coe : ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hα_coe, huj]
  have hθxj_coe : ((θ xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
    have e : θ xj = β uj := by rw [hβθ]; rfl
    rw [e, hβ_coe, huj]

  have hjb : ∃ jb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ((jb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) :=
    ⟨⟨jqModC (ResidueField ↥A), intFormRatiosC_subset (ResidueField ↥A) _ (jqModC_mem_intFormRatiosC (ResidueField ↥A) _)⟩, rfl⟩
  obtain ⟨jb, hjb_coe⟩ := hjb

  have h₁ : xj ∈ Rpd.R₁.integers ∧ ∀ h, Rpd.R₁.residue ⟨xj, h⟩ = jb := by
    have hval : coeffMap A.subtype (jqModC ↥A) = ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hxj_coe]
      exact map_jqModC A.subtype
    have hy : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
      rw [hval]
      exact xj.2
    obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hy
    have e : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(xHFunctionFieldBar M H)) = xj := Subtype.ext hval
    have hmem : xj ∈ Rpd.R₁.integers := e ▸ h
    refine ⟨hmem, fun h' => ?_⟩
    have e' : (⟨xj, h'⟩ : Rpd.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
    rw [e']
    apply Subtype.ext
    rw [hres, hjb_coe]
    exact map_jqModC (IsLocalRing.residue ↥A)
  have h₂ : xj ∈ Rpd.R₂.integers ∧ ∀ h, Rpd.R₂.residue ⟨xj, h⟩ = jb ^ p := by
    have hval : coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)) = ((θ xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hθxj_coe, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
      congr 1
      exact map_jqModC A.subtype
    have hy : coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)) ∈ xHFunctionFieldBar M H := by
      rw [hval]
      exact (θ xj).2
    obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap (qExpand ↥A p (jqModC ↥A)) hy
    have e : (⟨coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)), hy⟩ : ↥(xHFunctionFieldBar M H)) = θ xj := Subtype.ext hval
    have hθmem : θ xj ∈ Rpd.R₁.integers := e ▸ h
    have hmem : xj ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff xj).mpr hθmem
    refine ⟨hmem, fun h' => ?_⟩
    rw [Rpd.residue₂_eq xj h']
    have e' : (⟨θ xj, (Rpd.mem_integers₂_iff xj).mp h'⟩ : Rpd.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
    rw [e']
    apply Subtype.ext
    rw [hres, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, IntermediateField.coe_pow, hjb_coe]
    have hm : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC (IsLocalRing.residue ↥A)
    rw [hm]
    show qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) = jqModC (ResidueField ↥A) ^ p
    rw [jqModC_eq_map_intCast (ResidueField ↥A)]
    exact (map_intCast_pow_char_eq_qExpand p (jqModC ℤ)).symm

  have htr : Transcendental (ResidueField ↥A) jb := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible (ResidueField ↥A) (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp ((minpoly.degree_eq_one_iff (A := (ResidueField ↥A)) (x := jb)).mp hdeg)
    have h0 : algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c = jqModC (ResidueField ↥A) := by
      rw [← hjb_coe]; exact congrArg Subtype.val hc
    rw [algebraMap_laurentSeries_eq_single] at h0
    have hc2 := congrArg (fun s : LaurentSeries (ResidueField ↥A) => s.coeff (-1 : ℤ)) h0
    change (HahnSeries.single (0 : ℤ) c).coeff (-1 : ℤ) = (jqModC (ResidueField ↥A)).coeff (-1 : ℤ) at hc2
    rw [HahnSeries.coeff_single_of_ne (by decide : (-1 : ℤ) ≠ 0), coeff_jqModC_neg_one] at hc2
    exact zero_ne_one hc2

  have hdefect : Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({jb} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
      + Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({jb ^ p} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
      = Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xj} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) := by
    have h := DefectH.heq_core p M H hpM hpM2 hHp A hA θ α hα_coe hα Psp Rpd uj huj h₁.1 h₂.1
      ((h₂.2 _).trans (by rw [h₁.2]))
    rw [h₁.2 h₁.1, h₂.2 h₂.1] at h
    exact h
  haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xj} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) :=
    (transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC (AlgebraicClosure ℚ)
      (CohCarrier.GammaH M H) (translation_mem_GammaH M H) xj hxj_coe).2

  have hne : Rpd.R₁.integers ≠ Rpd.R₂.integers :=
    DefectH.integers_ne_integers p M H hpM hpM2 hHp A hA θ Psp Rpd xj h₁.1 h₂.1 jb hjb_coe (h₁.2 _) (h₂.2 _) htr

  let RR : Fin 2 → RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := ![Rpd.R₁, Rpd.R₂]
  have hRR0 : RR 0 = Rpd.R₁ := rfl
  have hRR1 : RR 1 = Rpd.R₂ := rfl
  have hinj : Function.Injective fun i => (RR i).integers := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl
  have hf : ∀ i, xj ∈ (RR i).integers := by
    intro i
    fin_cases i
    · exact h₁.1
    · exact h₂.1
  have hres : ∀ i, (RR i).residue ⟨xj, hf i⟩ = ![jb, jb ^ p] i := by
    intro i
    fin_cases i
    · exact h₁.2 _
    · exact h₂.2 _
  have htr' : ∀ i, Transcendental (ResidueField ↥A) ((RR i).residue ⟨xj, hf i⟩) := by
    intro i
    rw [hres]
    fin_cases i
    · exact htr
    · exact htr.pow (Fact.out : p.Prime).pos
  have heq : ∑ i, Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({(RR i).residue ⟨xj, hf i⟩} : Set (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
      = Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({xj} : Set ↥(xHFunctionFieldBar M H))) ↥(xHFunctionFieldBar M H) := by
    rw [Fin.sum_univ_two, hres, hres]
    exact hdefect
  obtain ⟨w, hwO, hwV, hli, -⟩ :=
    AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
      A (fun _ : Fin 2 => (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) RR hinj xj hf htr' heq (riemannRochSpace E)
  refine ⟨w, fun a => hwO a 0, fun a => hwO a 1, hwV, ?_⟩
  have h := hli.map' (LinearEquiv.finTwoArrow (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).toLinearMap (LinearEquiv.ker _)
  have hcomp : (⇑(LinearEquiv.finTwoArrow (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).toLinearMap ∘ fun a i => (RR i).residue ⟨w a, hwO a i⟩)
      = fun a => (Rpd.R₁.residue ⟨w a, hwO a 0⟩, Rpd.R₂.residue ⟨w a, hwO a 1⟩) := by
    funext a
    simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.finTwoArrow_apply]
    rfl
  rw [hcomp] at h
  exact h

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_basis_mem_integers_riemannRochSpace_linearIndependent_residue (solution)
