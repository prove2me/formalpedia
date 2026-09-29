-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/66a9518f-76c2-50d6-bb4e-a6ebbc1b0ff2

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isIntegrallyClosed_nodeIntegersOver
import Theorems.Thm_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length
import Theorems.Thm_ModularCurve_NodeLocalized_isDiscreteValuationRing_coeffSubring
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

universe u v

p2m_open "AlgebraicCurve IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve ModularCurve.UVCrossingModel ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve.PlaceSpecialization"

namespace ENat p2m_export "ENat" "card toNat one_le_iff_ne_zero map recTopCoe mul_top coe_ne_top" end ENat
p2m_open_scoped "ENat" in

theorem ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq
    {α : Type u} {X : Type v} (P : α → Prop) (C : X → α → Prop)
    (hCP : ∀ x a, C x a → P a) (hdisj : ∀ x x' a, C x a → C x' a → x = x')
    (F : α → ℕ∞) (hfin : {a | P a ∧ F a ≠ 0}.Finite) (T : Finset X) :
    (∑ x ∈ T, ∑ᶠ (a : α) (_ : C x a), F a) ≤ ∑ᶠ (a : α) (_ : P a), F a := by
  classical
  set S := hfin.toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ P a ∧ F a ≠ 0 := fun a => by rw [hS, Set.Finite.mem_toFinset]; rfl

  have hR : (∑ᶠ (a : α) (_ : P a), F a) = ∑ a ∈ S, (if P a then F a else 0) := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [finsum_eq_if]
    · intro a ha
      rw [Function.mem_support, finsum_eq_if] at ha
      rw [Finset.mem_coe, hmemS]
      by_cases hP : P a
      · rw [if_pos hP] at ha; exact ⟨hP, ha⟩
      · rw [if_neg hP] at ha; exact absurd rfl ha
  have hL : ∀ x, (∑ᶠ (a : α) (_ : C x a), F a) = ∑ a ∈ S, (if C x a then F a else 0) := by
    intro x
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [finsum_eq_if]
    · intro a ha
      rw [Function.mem_support, finsum_eq_if] at ha
      rw [Finset.mem_coe, hmemS]
      by_cases hC : C x a
      · rw [if_pos hC] at ha; exact ⟨hCP x a hC, ha⟩
      · rw [if_neg hC] at ha; exact absurd rfl ha
  rw [hR, Finset.sum_congr rfl (fun x _ => hL x), Finset.sum_comm]
  refine Finset.sum_le_sum fun a ha => ?_
  have hPa : P a := ((hmemS a).mp ha).1
  rw [if_pos hPa]

  by_cases hex : ∃ x ∈ T, C x a
  · obtain ⟨x, hxT, hxa⟩ := hex
    rw [Finset.sum_eq_single_of_mem x hxT]
    · rw [if_pos hxa]
    · intro y _ hyx
      rw [if_neg]
      intro hya
      exact hyx (hdisj y x a hya hxa)
  · push Not at hex
    rw [Finset.sum_eq_zero (fun y hy => if_neg (hex y hy))]
    exact zero_le

namespace NodeCountGlue

theorem length_localizedModule_quotient_eq_zero {R : Type u} [CommRing R] (x : R) (Q : Ideal R) [Q.IsPrime]
    (hx : x ∉ Q) : Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {x})) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine subsingleton_of_forall_eq 0 fun m => ?_
  induction m using LocalizedModule.induction_on with
  | h a s =>
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [Submonoid.smul_def, smul_zero]
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)

theorem sum_finsum_le_finsum_horizontal
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    {X : Type v} (T : Finset X) (κ : X → PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) → Prop)
    (hdisj : ∀ a b Q, κ a Q → κ b Q → a = b) :
    (∑ a ∈ T, ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ κ a Q),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  refine ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq
    (fun Q => Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal)
    (fun a Q => Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ κ a Q)
    (fun a Q h => ⟨h.1, h.2.1⟩) (fun a b Q h h' => hdisj a b Q h.2.2 h'.2.2) _ ?_ T
  refine (setOf_horizontal_mem_finite ϖ hϖ e he x hx).subset ?_
  rintro Q ⟨⟨h0, hc⟩, hF⟩
  refine ⟨h0, hc, ?_⟩
  by_contra hxQ
  apply hF
  rw [length_localizedModule_quotient_eq_zero x Q.asIdeal hxQ, mul_zero]

end NodeCountGlue

namespace NodeCountGlue

theorem mul_finsum_le_finsum_mul {α : Type u} (A B : α → Prop) (hAB : ∀ a, A a → B a) (hA : {a | A a}.Finite)
    (r m : α → ℕ∞) (ℓ : ℕ∞) (hℓ : ∀ a, A a → ℓ ≤ m a) (hfin : {a | B a ∧ r a * m a ≠ 0}.Finite) :
    ℓ * (∑ᶠ (a : α) (_ : A a), r a) ≤ ∑ᶠ (a : α) (_ : B a), r a * m a := by
  classical
  set S := hA.toFinset with hS
  have hmemS : ∀ a, a ∈ S ↔ A a := fun a => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hL : (∑ᶠ (a : α) (_ : A a), r a) = ∑ a ∈ S, r a := by
    rw [show (fun a => ∑ᶠ (_ : A a), r a) = fun a => ∑ᶠ (_ : a ∈ S), r a from
      funext fun a => by simp only [hmemS]]
    exact finsum_mem_finset_eq_sum r S
  have hM : (∑ᶠ (a : α) (_ : A a), r a * m a) = ∑ a ∈ S, r a * m a := by
    rw [show (fun a => ∑ᶠ (_ : A a), r a * m a) = fun a => ∑ᶠ (_ : a ∈ S), r a * m a from
      funext fun a => by simp only [hmemS]]
    exact finsum_mem_finset_eq_sum _ S
  calc ℓ * (∑ᶠ (a : α) (_ : A a), r a) = ∑ a ∈ S, ℓ * r a := by rw [hL, Finset.mul_sum]
    _ ≤ ∑ a ∈ S, r a * m a := Finset.sum_le_sum fun a ha => by
        rw [mul_comm]; exact mul_le_mul_right (hℓ a ((hmemS a).mp ha)) _
    _ = ∑ x ∈ ({()} : Finset Unit), ∑ᶠ (a : α) (_ : A a), r a * m a := by rw [Finset.sum_singleton, hM]
    _ ≤ ∑ᶠ (a : α) (_ : B a), r a * m a :=
        ENat.sum_finsum_le_finsum_of_forall_imp_of_forall_eq B (fun (_ : Unit) a => A a)
          (fun _ a h => hAB a h) (fun _ _ _ _ _ => rfl) _ hfin {()}

end NodeCountGlue

namespace IsLocalRing p2m_export "IsLocalRing" "isField_iff_maximalIdeal_eq le_maximalIdeal ResidueField maximalIdeal residue_eq_zero_iff maximalIdeal.isMaximal mem_maximalIdeal of_injective residue" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.ne_bot_and_comap_eq_of_map_le
    {B : Type u} [CommRing B] [IsLocalRing B] {Rm : Type v} [CommRing Rm] [IsDomain Rm]
    (j : B →+* Rm) (hj : Function.Injective j)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (𝔮 : Ideal B) [𝔮.IsPrime] (f : B) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (Q : Ideal Rm) [Q.IsPrime] (hJQ : Ideal.map j 𝔮 ≤ Q) (hQm : ∃ b ∈ maximalIdeal B, j b ∉ Q) :
    Q ≠ ⊥ ∧ Q.comap j = 𝔮 := by
  have hjf : j f ∈ Q := hJQ (Ideal.mem_map_of_mem j hf𝔮)
  refine ⟨fun hQ => hf (hj ?_), ?_⟩
  · rw [map_zero]
    rw [hQ] at hjf
    exact (Ideal.mem_bot.mp hjf)
  · have hle : 𝔮 ≤ Q.comap j := Ideal.le_comap_of_map_le hJQ
    haveI : (Q.comap j).IsPrime := Ideal.IsPrime.comap j
    have hne : Q.comap j ≠ maximalIdeal B := by
      obtain ⟨b, hb, hbQ⟩ := hQm
      intro h
      exact hbQ (show b ∈ Q.comap j from h ▸ hb)
    by_contra hneq
    have hlt : 𝔮 < Q.comap j := lt_of_le_of_ne hle (Ne.symm hneq)
    have := hht 𝔮 (Q.comap j) inferInstance inferInstance hne hlt
    exact hf (by rw [this] at hf𝔮; exact (Ideal.mem_bot.mp hf𝔮))

p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.algebraMap_adicCompletion_injective (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    Function.Injective (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
  change Function.Injective (AdicCompletion.of (maximalIdeal B) B)
  exact AdicCompletion.of_injective (maximalIdeal B) B

section MultStep
p2m_open "IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.IsLocalRing"

namespace LocLength

theorem length_localizedModule_quotient_span_singleton {A : Type u} [CommRing A] (p : Submonoid A) (a : A) :
    Module.length (Localization p) (LocalizedModule p (A ⧸ Ideal.span {a})) =
      Module.length (Localization p) (Localization p ⧸ Ideal.span {algebraMap A (Localization p) a}) := by

  rw [← (localizedQuotientEquiv p (Ideal.span {a} : Submodule A A)).length_eq]

  let e₀ : LocalizedModule p A ≃ₗ[A] Localization p :=
    IsLocalizedModule.iso p (Algebra.linearMap A (Localization p))
  let e : LocalizedModule p A ≃ₗ[Localization p] Localization p :=
    LinearEquiv.extendScalarsOfIsLocalization p (Localization p) e₀
  have he : ∀ x, e x = e₀ x := fun x => LinearEquiv.extendScalarsOfIsLocalization_apply p (Localization p) e₀ x
  have hmap : Submodule.map (e : LocalizedModule p A →ₗ[Localization p] Localization p)
      (Submodule.localized p (Ideal.span {a} : Submodule A A)) =
      (Ideal.span {algebraMap A (Localization p) a} : Submodule (Localization p) (Localization p)) := by
    change Submodule.map _ (Submodule.localized' (Localization p) p (LocalizedModule.mkLinearMap p A) (Submodule.span A {a})) = _
    rw [Submodule.localized'_span, Set.image_singleton, Submodule.map_span, Set.image_singleton, Ideal.span]
    congr 2
    change e (LocalizedModule.mk a 1) = _
    rw [he, IsLocalizedModule.iso_mk_one]
    rfl
  exact (Submodule.Quotient.equiv _ _ e hmap).length_eq

end LocLength

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "quotient mk maximalIdeal TFAE length_quotient_map_span_eq_length_mul_length" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in

theorem IsDiscreteValuationRing.length_localizedModule_quotient_le_of_comap_eq
    {B : Type u} [CommRing B] [IsDomain B] {R : Type v} [CommRing R] [IsDomain R]
    (j : B →+* R) (hj : Function.Injective j)
    (𝔮 : Ideal B) [𝔮.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔮)]
    (Q : Ideal R) [Q.IsPrime] (hcontr : Q.comap j = 𝔮) (f : B) (hf : f ≠ 0) :
    Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {f})) ≤
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl (R ⧸ Ideal.span {j f})) := by
  rw [LocLength.length_localizedModule_quotient_span_singleton, LocLength.length_localizedModule_quotient_span_singleton]
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors Q)
  let φ : Localization.AtPrime 𝔮 →+* Localization.AtPrime Q := Localization.localRingHom 𝔮 Q j hcontr.symm
  haveI : IsLocalHom φ := Localization.isLocalHom_localRingHom 𝔮 Q j hcontr.symm
  have hφ : ∀ d ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮), φ d ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
    fun d hd => map_nonunit φ d hd
  have hφ0 : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m, hm⟩, hma⟩ := hx
    have hm0 : m ≠ 0 := fun h => hm (by rw [h]; exact Q.zero_mem)
    have hja : j y.1 = 0 := (mul_eq_zero.mp hma).resolve_left hm0
    have ha : y.1 = 0 := hj (by rw [hja, map_zero])
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨1, by rw [ha, mul_zero]⟩
  have hfD : algebraMap B (Localization.AtPrime 𝔮) f ≠ 0 := by
    intro h
    rw [IsLocalization.map_eq_zero_iff 𝔮.primeCompl] at h
    obtain ⟨⟨s, hs⟩, hsf⟩ := h
    have : j s * j f = 0 := by rw [← map_mul, hsf, map_zero]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hs (by rw [hj (by rw [h1, map_zero] : j s = j 0)]; exact 𝔮.zero_mem)
    · exact hf (hj (by rw [h1, map_zero]))
  have hmult := IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length φ hφ0 _ hfD
  rw [Localization.localRingHom_to_map] at hmult
  rw [hmult]

  have hne : Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) ≠ ⊤ := by
    intro h
    have hle : Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
      Ideal.map_le_iff_le_comap.mpr (fun d hd => hφ d hd)
    rw [h, top_le_iff] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime Q)).ne_top hle
  haveI : Nontrivial (Localization.AtPrime Q ⧸ Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have h1 : 1 ≤ Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ Ideal.map φ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮))) := by
    rw [ENat.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff]
    exact not_subsingleton _
  calc Module.length (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap B _ f})
      = Module.length (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap B _ f}) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right h1 _

end MultStep

namespace SepAux

theorem isDiscreteValuationRing_localization {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (𝔮 : Ideal B) [𝔮.IsPrime] (hbot : 𝔮 ≠ ⊥)
    (hht : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime 𝔮) := by
  haveI : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance
  have hinjB := IsLocalization.injective (Localization.AtPrime 𝔮) 𝔮.primeCompl_le_nonZeroDivisors
  have hunder : Ideal.under B (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮)) = 𝔮 :=
    IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime 𝔮) 𝔮
  have hnf : ¬ IsField (Localization.AtPrime 𝔮) := by
    intro hf
    apply hbot
    have h1 : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq).mp hf
    rw [← hunder, h1]
    exact Ideal.comap_bot_of_injective _ hinjB
  have hic : IsIntegrallyClosed (Localization.AtPrime 𝔮) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime 𝔮) 𝔮.primeCompl 𝔮.primeCompl_le_nonZeroDivisors
  have key : IsIntegrallyClosed (Localization.AtPrime 𝔮) ∧
      ∃! P : Ideal (Localization.AtPrime 𝔮), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨hic, IsLocalRing.maximalIdeal _, ⟨?_, inferInstance⟩, ?_⟩
    · exact fun h0 => hnf ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h0)
    · rintro P ⟨hP0, hP⟩
      have hPq : Ideal.under B P ≤ 𝔮 :=
        (Ideal.comap_mono (f := algebraMap B (Localization.AtPrime 𝔮)) (IsLocalRing.le_maximalIdeal hP.ne_top)).trans_eq hunder
      have hPpr : (Ideal.under B P).IsPrime := Ideal.comap_isPrime _ P
      have hne : Ideal.under B P ≠ ⊥ := by
        intro h0
        apply hP0
        rw [← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) P]
        show Ideal.map _ (Ideal.under B P) = ⊥
        rw [h0, Ideal.map_bot]
      have heq : Ideal.under B P = 𝔮 := by
        rcases eq_or_lt_of_le hPq with h | h
        · exact h
        · exact absurd (hht _ hPpr h) hne
      rw [← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) P,
        ← IsLocalization.map_comap 𝔮.primeCompl (Localization.AtPrime 𝔮) (IsLocalRing.maximalIdeal _)]
      show Ideal.map _ (Ideal.under B P) = Ideal.map _ (Ideal.under B (IsLocalRing.maximalIdeal _))
      rw [heq, hunder]
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime 𝔮) hnf).out 0 3).mpr key

end SepAux

namespace NodeCountGlue
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve ModularCurve.UVCrossingModel"

theorem le_finsum_of_le_mul_finsum
    {B : Type v} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (j : B →+* UVCrossingModel W (π ^ E)) (hj : Function.Injective j)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (b₀ : B) (hb₀ : b₀ ∈ maximalIdeal B) (hjb₀ : j b₀ = const (π ^ E) π)
    (𝔮 : Ideal B) [𝔮.IsPrime] (hne : 𝔮 ≠ maximalIdeal B) (f : B) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (X : ℕ∞)
    (h1 : X ≤ Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {f})) *
        ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞)) :
    X ≤ ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (π ^ E) ⧸ Ideal.span {j f})) := by
  classical
  haveI : IsDomain (UVCrossingModel W (π ^ E)) :=
    (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete π hπ E hE).1
  refine h1.trans ?_
  have hjf0 : j f ≠ 0 := fun h0 => hf (hj (by rw [h0, map_zero]))
  have hcontr : ∀ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal →
      Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮 := by
    rintro Q ⟨hQmin, hQπ⟩
    have hJQ : Ideal.map j 𝔮 ≤ Q.asIdeal := hQmin.1.2
    have hQm : ∃ b ∈ maximalIdeal B, j b ∉ Q.asIdeal := ⟨b₀, hb₀, fun h => hQπ (hjb₀ ▸ h)⟩
    obtain ⟨h0, hc⟩ := IsLocalRing.ne_bot_and_comap_eq_of_map_le j hj hht 𝔮 f hf hf𝔮 Q.asIdeal hJQ hQm
    exact ⟨h0, hQπ, hc⟩
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔮) :=
    SepAux.isDiscreteValuationRing_localization 𝔮 (fun h0 => hf (by rw [h0] at hf𝔮; exact Ideal.mem_bot.mp hf𝔮))
      fun 𝔭 h𝔭 hlt => hht 𝔭 𝔮 h𝔭 inferInstance hne hlt
  refine mul_finsum_le_finsum_mul
    (fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
      Q.asIdeal ∈ (Ideal.map j 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal)
    (fun Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) =>
      Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧ Q.asIdeal.comap j = 𝔮)
    hcontr ?_ _ _ _ ?_ ?_
  · refine (setOf_horizontal_mem_finite π hπ E hE (j f) hjf0).subset ?_
    intro Q hQ
    exact ⟨(hcontr Q hQ).1, hQ.2, hQ.1.1.2 (Ideal.mem_map_of_mem j hf𝔮)⟩
  · rintro Q hQ
    haveI := Q.2
    exact IsDiscreteValuationRing.length_localizedModule_quotient_le_of_comap_eq j hj 𝔮 Q.asIdeal (hcontr Q hQ).2.2 f hf
  · refine (setOf_horizontal_mem_finite π hπ E hE (j f) hjf0).subset ?_
    rintro Q ⟨⟨h0, hc, -⟩, hF⟩
    refine ⟨h0, hc, ?_⟩
    by_contra hxQ
    apply hF
    rw [length_localizedModule_quotient_eq_zero _ Q.asIdeal hxQ, mul_zero]

end NodeCountGlue

namespace NodeCountGlue
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve.PlaceSpecialization ModularCurve.UVCrossingModel ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve.PlaceSpecialization.ProlongationTuple"

theorem sum_toNat_ord_le_finsum_of_comap_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime]
    (h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮)
    (f : ↥(R.nodeIntegersOver K w)) (hf : f ≠ 0) (hf𝔮 : f ∈ 𝔮)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0)
    (hne : 𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) :
    ((∑ V ∈ S, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))) = 𝔮),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {(ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) f})) := by
  haveI := R.isIntegrallyClosed_nodeIntegersOver K w
  refine le_finsum_of_le_mul_finsum π hπ E hE _
    (ι.injective.comp (IsLocalRing.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w)))
    hht (R.nodeConst K w ϖ) (by rw [hmax]; exact Ideal.subset_span (by simp)) hιϖ 𝔮 hne f hf hf𝔮 _ ?_
  exact R.sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres hVI
    hwss π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 f hf hf𝔮 S hS

end NodeCountGlue

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces arithFrobC NodeLocalized.coeffSubring NodeLocalized.fieldOver UVCrossingModel UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete isCurveOver_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.nodeResidue₁_apply ProlongationTuple.nodeResidue₂_apply ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst mk"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw nodeIntegers mem_toValuationSubring_of_mem_nodeIntegers nodeResidue₁ nodeResidue₂ nodeResidue₁_apply nodeResidue₂_apply nodeIntegersOver nodeIntegersOver_le nodeConst NodeCoordinates residue₁_apply residue₂_apply OrderLawFixed R₁ mk ι R₂ ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem isIntegrallyClosed_nodeIntegersOver sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

section SepGlue

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem isRational_of_place (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : V.IsRational := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)

theorem valuation_sub_evalAt_lt_one (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ V.toValuationSubring) :
    V.toValuationSubring.valuation
      (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f)) < 1 := by
  have hV := isRational_of_place V
  have hmem : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f) ∈ V.toValuationSubring :=
    sub_mem hf (V.algebraMap_mem' _)
  rw [show (f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt f)) =
      ((⟨_, hmem⟩ : V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff]
  have h1 := V.algebraMap_evalAt hV hf
  have h2 := V.residue_algebraMap (V.evalAt f)
  have : (⟨_, hmem⟩ : V.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap (AlgebraicClosure ℚ) _ (V.evalAt f), V.algebraMap_mem' _⟩ := rfl
  rw [this, map_sub, sub_eq_zero, ← h1]
  exact h2.symm

theorem evalAt_eq_zero_iff (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    {f : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ V.toValuationSubring) :
    V.evalAt f = 0 ↔ V.toValuationSubring.valuation f < 1 := by
  have hV := isRational_of_place V
  rw [show (f : ↥(modularFunctionFieldBar (N * q))) = ((⟨f, hf⟩ : V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) from rfl,
    ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, ← V.algebraMap_evalAt hV hf,
    map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective]

end SepGlue

end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ENatSqueeze

theorem eq_of_forall_le_of_sum_le {α : Type*} [DecidableEq α] (I : Finset α) (a b : α → ℕ∞)
    (hle : ∀ i ∈ I, a i ≤ b i) (hsum : ∑ i ∈ I, b i ≤ ∑ i ∈ I, a i) (hfin : ∑ i ∈ I, a i ≠ ⊤) :
    ∀ i ∈ I, a i = b i := by
  intro j hj
  by_contra hne
  have hlt : a j < b j := lt_of_le_of_ne (hle j hj) hne
  have hrest : ∑ i ∈ I.erase j, a i ≤ ∑ i ∈ I.erase j, b i :=
    Finset.sum_le_sum fun i hi => hle i (Finset.mem_of_mem_erase hi)
  have hrestfin : ∑ i ∈ I.erase j, a i ≠ ⊤ := by
    intro htop
    apply hfin
    rw [← Finset.add_sum_erase I a hj, htop, add_top]
  have h1 : ∑ i ∈ I, a i < ∑ i ∈ I, b i := by
    rw [← Finset.add_sum_erase I a hj, ← Finset.add_sum_erase I b hj]
    calc a j + ∑ i ∈ I.erase j, a i < b j + ∑ i ∈ I.erase j, a i := WithTop.add_lt_add_right hrestfin hlt
      _ ≤ b j + ∑ i ∈ I.erase j, b i := add_le_add le_rfl hrest
  exact absurd hsum (not_le.mpr h1)

theorem natCast_eq_of_natCast_mul_eq_mul (m s : ℕ) (hm : m ≠ 0) (t : ℕ∞)
    (h : (s : ℕ∞) * (m : ℕ∞) = (m : ℕ∞) * t) : (s : ℕ∞) = t := by
  induction t using ENat.recTopCoe with
  | top =>
    exfalso
    have h1 : (m : ℕ∞) * ⊤ = ⊤ := ENat.mul_top (by exact_mod_cast hm)
    rw [h1] at h
    exact ENat.coe_ne_top (s * m) (by exact_mod_cast h)
  | coe r =>
    have h' : s * m = m * r := by exact_mod_cast h
    have hsr : s = r := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) (by rwa [mul_comm] at h')
    rw [hsr]

end ENatSqueeze

set_option maxHeartbeats 6400000 in
open AlgebraicCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero.ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.UVCrossingModel Valued in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime]
    (h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮)
    (h𝔮0 : 𝔮 ≠ ⊥)
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (hιord₁ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hιord₂ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V, V ∈ S ↔ (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0)) :
    (S.card : ℕ∞) = ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
            const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by
  classical
  haveI hIC := R.isIntegrallyClosed_nodeIntegersOver K w

  have hϖm : R.nodeConst K w ϖ ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
    rw [hmax]; exact Ideal.subset_span (by simp)
  have hne : 𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := fun h => h𝔮 ϖ hϖ0 (h ▸ hϖm)

  let r₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  let r₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hr₁ : ∀ g : ↥(R.nodeIntegersOver K w), r₁ g = R.nodeResidue₁ w ⟨g, g.2.1⟩ := fun g => rfl
  have hr₂ : ∀ g : ↥(R.nodeIntegersOver K w), r₂ g = R.nodeResidue₂ w ⟨g, g.2.1⟩ := fun g => rfl

  have hϖA : IsLocalRing.residue A ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) := by
      rw [hϖgen]; exact Ideal.mem_span_singleton_self ϖ
    apply (IsLocalRing.mem_maximalIdeal _).mp hϖmax
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbval : ((b : A) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ)⁻¹ := by
      have h1 : (ϖ : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hb
        simpa using this
      have hϖ0' : (ϖ : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
      field_simp
      rw [mul_comm]; exact h1
    have hinvK : (ϖ : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem ϖ.2.2
    have hinvA : (ϖ : AlgebraicClosure ℚ)⁻¹ ∈ A := hbval ▸ (b : A).2
    refine ⟨⟨ϖ, ⟨(ϖ : AlgebraicClosure ℚ)⁻¹, ⟨hinvA, hinvK⟩⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (ϖ : AlgebraicClosure ℚ) * (ϖ : AlgebraicClosure ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ (fun h0 => by rw [h0, inv_zero] at hbval; exact hϖ0 (Subtype.ext (by
        have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hb
        simp [hbval] at this)))
    · apply Subtype.ext
      show (ϖ : AlgebraicClosure ℚ)⁻¹ * (ϖ : AlgebraicClosure ℚ) = 1
      exact inv_mul_cancel₀ (fun h0 => by rw [h0, inv_zero] at hbval; exact hϖ0 (Subtype.ext (by
        have := congrArg (fun t : A => (t : AlgebraicClosure ℚ)) hb
        simp [hbval] at this)))

  have hres₁ϖ : r₁ (R.nodeConst K w ϖ) = 0 := by
    have h := R.R₁.residue_algebraMap ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩
    rw [hϖA, map_zero] at h
    rw [hr₁, ProlongationTuple.nodeResidue₁_apply, ProlongationTuple.residue₁_apply]
    have hmk : (⟨((⟨(R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)), (R.nodeConst K w ϖ).2.1⟩ : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K w ϖ).2.1.1⟩ : ↥R.R₁.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ),
          (R.R₁.algebraMap_mem_iff _).mpr (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A).2⟩ := rfl
    rw [hmk, h, map_zero]
  have hres₂ϖ : r₂ (R.nodeConst K w ϖ) = 0 := by
    have h := R.R₂.residue_algebraMap ⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩
    rw [hϖA, map_zero] at h
    rw [hr₂, ProlongationTuple.nodeResidue₂_apply, ProlongationTuple.residue₂_apply]
    have hmk : (⟨((⟨(R.nodeConst K w ϖ : ↥(R.nodeIntegersOver K w)), (R.nodeConst K w ϖ).2.1⟩ : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q))), (R.nodeConst K w ϖ).2.1.2.1⟩ : ↥R.R₂.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) : AlgebraicClosure ℚ),
          (R.R₂.algebraMap_mem_iff _).mpr (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A).2⟩ := rfl
    rw [hmk, h, map_zero]

  have hx2 : r₂ c.x ≠ 0 := by
    intro h0
    have h1 := c.x_snd
    rw [← hr₂, h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hy1 : r₁ c.y ≠ 0 := by
    intro h0
    have h1 := c.y_fst
    rw [← hr₁, h0, Place.ord_zero] at h1
    exact zero_ne_one h1

  obtain ⟨f₀, hf₀𝔮, hf₀1, hf₀2⟩ : ∃ f₀ ∈ 𝔮, r₁ f₀ ≠ 0 ∧ r₂ f₀ ≠ 0 := by
    by_contra hcon
    have hsub : ((𝔮 : Ideal ↥(R.nodeIntegersOver K w)) : Set ↥(R.nodeIntegersOver K w)) ⊆
        (RingHom.ker r₁ : Set ↥(R.nodeIntegersOver K w)) ∪ (RingHom.ker r₂ : Set ↥(R.nodeIntegersOver K w)) := by
      intro g hg
      by_cases h1 : r₁ g = 0
      · exact Or.inl h1
      · by_cases h2 : r₂ g = 0
        · exact Or.inr h2
        · exact absurd ⟨g, hg, h1, h2⟩ hcon
    have key : ∀ (r : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N)) (z : ↥(R.nodeIntegersOver K w)),
        z ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → r z ≠ 0 → r (R.nodeConst K w ϖ) = 0 →
        ¬ 𝔮 ≤ RingHom.ker r := by
      intro r z hz hrz hrϖ hle
      have hne1 : RingHom.ker r ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
        intro h
        have hz' : z ∈ RingHom.ker r := by rw [h]; exact hz
        exact hrz (RingHom.mem_ker.mp hz')
      have hlt : 𝔮 < RingHom.ker r := lt_of_le_of_ne hle (fun h => h𝔮 ϖ hϖ0 (by rw [h]; exact hrϖ))
      exact h𝔮0 (hht 𝔮 _ inferInstance (RingHom.ker_isPrime r) hne1 hlt)
    have hym : c.y ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
      rw [hmax]; exact Ideal.subset_span (by simp)
    have hxm : c.x ∈ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) := by
      rw [hmax]; exact Ideal.subset_span (by simp)
    rcases Ideal.subset_union.mp hsub with hle | hle
    · exact key r₁ c.y hym hy1 hres₁ϖ hle
    · exact key r₂ c.x hxm hx2 hres₂ϖ hle

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (w.ord (r₁ f₀)).natAbs + ((arithFrobC q k N • w).ord (r₂ f₀)).natAbs ≤ n := ⟨_, le_rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ↥(R.nodeIntegersOver K w), f = f₀ * (c.x + c.y) ^ n := ⟨_, rfl⟩
  have hf𝔮 : f ∈ 𝔮 := by rw [hfdef]; exact Ideal.mul_mem_right _ _ hf₀𝔮
  have hr₁x : r₁ c.x = 0 := c.x_fst
  have hr₂y : r₂ c.y = 0 := c.y_snd
  have hr₁f : r₁ f = r₁ f₀ * (r₁ c.y) ^ n := by
    rw [hfdef, map_mul, map_pow, map_add, hr₁x, zero_add]
  have hr₂f : r₂ f = r₂ f₀ * (r₂ c.x) ^ n := by
    rw [hfdef, map_mul, map_pow, map_add, hr₂y, add_zero]
  have hr₁f0 : r₁ f ≠ 0 := by rw [hr₁f]; exact mul_ne_zero hf₀1 (pow_ne_zero _ hy1)
  have hr₂f0 : r₂ f ≠ 0 := by rw [hr₂f]; exact mul_ne_zero hf₀2 (pow_ne_zero _ hx2)
  have h₁ : R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0 := by rw [← hr₁]; exact hr₁f0
  have h₂ : R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0 := by rw [← hr₂]; exact hr₂f0
  have hf : f ≠ 0 := fun h0 => hr₁f0 (by rw [h0, map_zero])
  have ha : 0 ≤ w.ord (R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) := by
    rw [← hr₁, hr₁f, w.ord_mul hf₀1 (pow_ne_zero _ hy1), ← zpow_natCast, w.ord_zpow]
    have hy : w.ord (r₁ c.y) = 1 := c.y_fst
    rw [hy, mul_one]
    omega
  have hb : 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) := by
    rw [← hr₂, hr₂f, (arithFrobC q k N • w).ord_mul hf₀2 (pow_ne_zero _ hx2), ← zpow_natCast, (arithFrobC q k N • w).ord_zpow]
    have hx : (arithFrobC q k N • w).ord (r₂ c.x) = 1 := c.x_snd
    rw [hx, mul_one]
    omega

  haveI hPD := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar ModularCurve.modularPolynomialFamily (N * q)
  have hfF : ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) ≠ 0 :=
    fun h => hf (Subtype.ext h)
  obtain ⟨D, hD, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) hfF
  obtain ⟨Ttot, hTtot⟩ : ∃ Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w) :=
    ⟨D.support.filter (fun V => P.reduceFst V = w), fun V => by
      rw [Finset.mem_filter, Finsupp.mem_support_iff, hD V]⟩

  have htot := R.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero K w c ϖ hmax hres hVI hwss
    π hπ E hE ι hιϖ αU hαU hιx f hqN hO h₁ h₂ hιord₁ hιord₂ ha hb Ttot hTtot

  have hmemV : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.reduceFst V = w →
      ∀ g : ↥(R.nodeIntegersOver K w), (g : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    fun V hV g => R.mem_toValuationSubring_of_mem_nodeIntegers g.2.1 hV
  obtain ⟨ker, hker⟩ : ∃ ker : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → Ideal ↥(R.nodeIntegersOver K w),
      ∀ V, P.reduceFst V = w → ∀ g : ↥(R.nodeIntegersOver K w),
        g ∈ ker V ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0 := by
    refine ⟨fun V => if hV : P.reduceFst V = w then
      (IsLocalRing.maximalIdeal ↥V.toValuationSubring).comap
        ((R.nodeIntegersOver K w).subtype.codRestrict V.toValuationSubring.toSubring (fun g => hmemV V hV g))
      else ⊥, ?_⟩
    intro V hV g
    simp only [dif_pos hV, Ideal.mem_comap]
    rw [ValuationSubring.valuation_lt_one_iff, evalAt_eq_zero_iff V (hmemV V hV g)]
    rfl
  have hkerV : ∀ V ∈ Ttot, P.reduceFst V = w ∧ (ker V).IsPrime ∧
      ker V ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ ker V) ∧ f ∈ ker V := by
    intro V hV
    obtain ⟨hord, hVw⟩ := (hTtot V).mp hV
    obtain ⟨h1, h2, h3, h4⟩ :=
      R.ker_evalAt_isPrime_and_ne_maximalIdeal_and_nodeConst_notMem K w V hVw (ker V) (hker V hVw)
    exact ⟨hVw, h1, h2, h3, h4 f hord⟩

  obtain ⟨I, h𝔮I, hTI, hIsub⟩ : ∃ I : Finset (Ideal ↥(R.nodeIntegersOver K w)), 𝔮 ∈ I ∧ (∀ V ∈ Ttot, ker V ∈ I) ∧
      (∀ 𝔮' ∈ I, 𝔮' = 𝔮 ∨ ∃ V ∈ Ttot, ker V = 𝔮') := by
    refine ⟨insert 𝔮 (Ttot.image ker), Finset.mem_insert_self _ _,
      fun V hV => Finset.mem_insert_of_mem (Finset.mem_image_of_mem ker hV), fun 𝔮' h => ?_⟩
    rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl h
    · obtain ⟨V, hV, hVe⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨V, hV, hVe⟩
  have hI : ∀ 𝔮' ∈ I, 𝔮'.IsPrime ∧ 𝔮' ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) ∧
      (∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮') ∧ f ∈ 𝔮' ∧
      (∀ V ∈ Ttot.filter (fun V => ker V = 𝔮'), P.reduceFst V = w ∧
        ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮' ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0) := by
    intro 𝔮' h𝔮'
    have hfib : ∀ V ∈ Ttot.filter (fun V => ker V = 𝔮'), P.reduceFst V = w ∧
        ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮' ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0 := by
      intro V hV
      rw [Finset.mem_filter] at hV
      obtain ⟨hVw, -, -, -, -⟩ := hkerV V hV.1
      exact ⟨hVw, fun g => hV.2 ▸ hker V hVw g⟩
    rcases hIsub 𝔮' h𝔮' with h | ⟨V₀, hV₀, hV₀eq⟩
    · subst h
      exact ⟨inferInstance, hne, h𝔮, hf𝔮, hfib⟩
    · obtain ⟨-, hpr, hne', hcst, hfV⟩ := hkerV V₀ hV₀
      rw [hV₀eq] at hpr hne' hcst hfV
      exact ⟨hpr, hne', hcst, hfV, hfib⟩

  obtain ⟨Aq, hAq⟩ : ∃ Aq : Ideal ↥(R.nodeIntegersOver K w) → ℕ∞, ∀ 𝔮', Aq 𝔮' =
      ((∑ V ∈ Ttot.filter (fun V => ker V = 𝔮'), (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Cq, hCq⟩ : ∃ Cq : Ideal ↥(R.nodeIntegersOver K w) → ℕ∞, ∀ 𝔮', Cq 𝔮' =
    ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal ∧
        (Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
          (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))) = 𝔮'),
      (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime Q.asIdeal)
          (LocalizedModule Q.asIdeal.primeCompl
            (UVCrossingModel W (π ^ E) ⧸ Ideal.span {(ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) f})) :=
    ⟨_, fun _ => rfl⟩
  have hAC : ∀ 𝔮' ∈ I, Aq 𝔮' ≤ Cq 𝔮' := by
    intro 𝔮' h𝔮'
    obtain ⟨hpr, hne', hcst, hfq, hfib⟩ := hI 𝔮' h𝔮'
    haveI := hpr
    rw [hAq, hCq]
    exact NodeCountGlue.sum_toNat_ord_le_finsum_of_comap_eq R K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx
      hht hfrac hϖgen τ hτ hτϖ 𝔮' hcst f hf hfq (Ttot.filter (fun V => ker V = 𝔮')) hfib hne'
  have hjf : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) f ≠ 0 := by
    intro h0
    apply hf
    apply ι.injective.comp (IsLocalRing.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w))
    show ι (algebraMap _ _ f) = ι (algebraMap _ _ 0)
    rw [map_zero, map_zero]
    exact h0
  have hCtot := NodeCountGlue.sum_finsum_le_finsum_horizontal π hπ E hE _ hjf I
    (fun 𝔮' Q => Q.asIdeal.comap (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) = 𝔮')
    (fun a b Q ha hb => ha.symm.trans hb)
  have hsplit : ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) = ∑ 𝔮' ∈ I, Aq 𝔮' := by
    rw [Finset.sum_congr rfl (fun 𝔮' _ => hAq 𝔮'), ← Finset.sum_fiberwise_of_maps_to (s := Ttot) (t := I) (g := ker) hTI,
      Nat.cast_sum]
  have hsumle : ∑ 𝔮' ∈ I, Cq 𝔮' ≤ ∑ 𝔮' ∈ I, Aq 𝔮' := by
    rw [← hsplit, Finset.sum_congr rfl (fun 𝔮' _ => hCq 𝔮')]
    refine hCtot.trans (le_of_eq ?_)
    exact htot.symm
  have hfinA : ∑ 𝔮' ∈ I, Aq 𝔮' ≠ ⊤ := by
    rw [← hsplit]
    exact ENat.coe_ne_top _
  have hAeqC := ENatSqueeze.eq_of_forall_le_of_sum_le I Aq Cq hAC hsumle hfinA

  obtain ⟨-, -, -, -, hfib𝔮⟩ := hI 𝔮 h𝔮I
  have hAB : Aq 𝔮 ≤ Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {f})) *
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
          const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) := by
    rw [hAq]
    exact R.sum_toNat_ord_le_length_mul_finsum_finrank_of_forall_mem_iff_evalAt_eq_zero K w c ϖ hϖ0 hmax hres hVI
      hwss π hπ E hE ι hιϖ αU hαU hιx hht hfrac hϖgen τ hτ hτϖ 𝔮 h𝔮 f hf hf𝔮 (Ttot.filter (fun V => ker V = 𝔮)) hfib𝔮
  have hBC := NodeCountGlue.le_finsum_of_le_mul_finsum π hπ E hE
    (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))))
    (ι.injective.comp (IsLocalRing.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w)))
    hht (R.nodeConst K w ϖ) hϖm hιϖ 𝔮 hne f hf hf𝔮 _ le_rfl
  have hmain : Aq 𝔮 = Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {f})) *
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
            (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
          const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) :=
    le_antisymm hAB (hBC.trans (by rw [← hCq, ← hAeqC 𝔮 h𝔮I, hAq]))

  have hSeq : S = Ttot.filter (fun V => ker V = 𝔮) := by
    ext V
    rw [hS V, Finset.mem_filter, hTtot V]
    constructor
    · rintro ⟨hVw, hq⟩
      have hkq : ker V = 𝔮 := by
        ext g
        rw [hker V hVw g, hq g]
      refine ⟨⟨?_, hVw⟩, hkq⟩
      intro hord
      have hev : V.evalAt ((f : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = 0 := (hq f).mp hf𝔮
      exact (V.evalAt_ne_zero (isRational_of_place V) hfF hord) hev
    · rintro ⟨⟨-, hVw⟩, hkq⟩
      exact ⟨hVw, fun g => by rw [← hkq]; exact hker V hVw g⟩

  have hℓ : ∀ V ∈ Ttot.filter (fun V => ker V = 𝔮), ((V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ∞) =
      Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {f})) :=
    fun V hV => R.toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero K w hfrac V
      (hfib𝔮 V hV).1 𝔮 (hfib𝔮 V hV).2 (fun 𝔭 h𝔭 hlt => hht 𝔭 𝔮 h𝔭 inferInstance hne hlt) f hf

  have hℓ0 : Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {f})) ≠ 0 := by
    rw [LocLength.length_localizedModule_quotient_span_singleton]
    intro h0
    rw [Module.length_eq_zero_iff] at h0
    have hnt : Nontrivial (Localization.AtPrime 𝔮 ⧸
        Ideal.span {algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮) f}) := by
      rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.span_singleton_eq_top]
      intro hu
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔮) 𝔮 f).mp hu) hf𝔮
    haveI := h0
    haveI := hnt
    exact false_of_nontrivial_of_subsingleton
      (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮) f})

  rw [hAq] at hmain
  rw [hSeq]
  rcases (Ttot.filter (fun V => ker V = 𝔮)).eq_empty_or_nonempty with hSe | ⟨V₀, hV₀⟩
  · rw [hSe, Finset.sum_empty, Nat.cast_zero] at hmain
    rw [hSe, Finset.card_empty, Nat.cast_zero]
    exact ((mul_eq_zero.mp hmain.symm).resolve_left hℓ0).symm
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, Module.length (Localization.AtPrime 𝔮)
        (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {f})) = m := ⟨_, (hℓ V₀ hV₀).symm⟩
    have hsumN : ∑ V ∈ Ttot.filter (fun V => ker V = 𝔮), (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat =
        (Ttot.filter (fun V => ker V = 𝔮)).card * m := by
      rw [Finset.sum_eq_card_nsmul (b := m) (fun V hV => ?_), smul_eq_mul]
      have h2 := (hℓ V hV).trans hm
      exact_mod_cast h2
    rw [hsumN, hm, Nat.cast_mul] at hmain
    have hm0 : m ≠ 0 := by
      intro h0
      exact hℓ0 (by rw [hm, h0, Nat.cast_zero])
    exact ENatSqueeze.natCast_eq_of_natCast_mul_eq_mul m _ hm0 _ hmain

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_eq_finsum_finrank_quotient_of_forall_iff_evalAt_eq_zero (solution)
