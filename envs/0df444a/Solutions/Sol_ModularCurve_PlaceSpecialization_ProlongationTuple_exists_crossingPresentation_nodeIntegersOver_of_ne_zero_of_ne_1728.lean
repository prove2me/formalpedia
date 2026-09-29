-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e6a85cd6-827f-557f-98c2-d1f50f6c2701

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace NodeCrossingAux

section RingHalf

variable {B : Type*} [CommRing B] {k : Type*} [Field k]
variable {D₁ : Type*} [CommRing D₁] [IsDomain D₁] {D₂ : Type*} [CommRing D₂] [IsDomain D₂]
variable (χ : B →+* k) (ρ₁ : B →+* D₁) (ρ₂ : B →+* D₂) (e₁ : D₁ →+* k) (e₂ : D₂ → k)
variable (ϖ x y : B)

private theorem mem_span_triple_iff (a b c g : B) :
    g ∈ Ideal.span ({a, b, c} : Set B) ↔ ∃ p q r : B, p * a + q * b + r * c = g := by
  constructor
  · intro hg
    rcases Ideal.mem_span_insert.mp hg with ⟨p, z, hz, rfl⟩
    rcases Ideal.mem_span_pair.mp hz with ⟨q, r, rfl⟩
    exact ⟨p, q, r, by ring⟩
  · rintro ⟨p, q, r, rfl⟩
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

private theorem mem_span_pair_iff' (a b g : B) :
    g ∈ Ideal.span ({a, b} : Set B) ↔ ∃ p q : B, p * a + q * b = g :=
  Ideal.mem_span_pair

omit [IsDomain D₁] [IsDomain D₂] in

private theorem span_triple_eq_ker
    (he₁ : e₁.comp ρ₁ = χ) (he₂ : ∀ g : B, e₂ (ρ₂ g) = χ g) (he₂0 : e₂ 0 = 0)
    (hϖ₁ : ρ₁ ϖ = 0) (hx₁ : ρ₁ x = 0) (hy₂ : ρ₂ y = 0)
    (hsat₁ : ∀ g : B, e₁ (ρ₁ g) = 0 → ∃ b : B, ρ₁ g = ρ₁ y * ρ₁ b)
    (hsat₂ : ∀ g : B, e₂ (ρ₂ g) = 0 → ∃ b : B, ρ₂ g = ρ₂ x * ρ₂ b)
    (hker : ∀ g : B, ρ₁ g = 0 → ρ₂ g = 0 → ∃ b : B, g = ϖ * b) :
    Ideal.span ({ϖ, x, y} : Set B) = RingHom.ker χ := by
  have hχϖ : χ ϖ = 0 := by rw [← he₁, RingHom.comp_apply, hϖ₁, map_zero]
  have hχx : χ x = 0 := by rw [← he₁, RingHom.comp_apply, hx₁, map_zero]
  have hχy : χ y = 0 := by rw [← he₂, hy₂, he₂0]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (rfl | rfl | rfl) <;> simpa [RingHom.mem_ker]
  · intro g hg
    rw [RingHom.mem_ker] at hg

    have h1 : e₁ (ρ₁ g) = 0 := by rw [← RingHom.comp_apply, he₁, hg]
    obtain ⟨b, hb⟩ := hsat₁ g h1

    have h2 : e₂ (ρ₂ (g - y * b)) = 0 := by
      rw [he₂, map_sub, map_mul, hg, hχy, zero_mul, sub_zero]
    obtain ⟨b', hb'⟩ := hsat₂ (g - y * b) h2
    have hρ₁ : ρ₁ (g - y * b - x * b') = 0 := by
      rw [map_sub, map_sub, map_mul, map_mul, hb, hx₁, zero_mul, sub_zero, sub_self]
    have hρ₂ : ρ₂ (g - y * b - x * b') = 0 := by
      rw [map_sub, map_mul, hb', sub_self]
    obtain ⟨b'', hb''⟩ := hker _ hρ₁ hρ₂
    rw [mem_span_triple_iff]
    exact ⟨b'', b', b, by linear_combination -hb''⟩

omit [IsDomain D₁] [IsDomain D₂] in

private theorem span_triple_isMaximal_and_unique
    (he₁ : e₁.comp ρ₁ = χ) (he₂ : ∀ g : B, e₂ (ρ₂ g) = χ g) (he₂0 : e₂ 0 = 0)
    (hunit : ∀ g : B, χ g ≠ 0 → IsUnit g)
    (hϖ₁ : ρ₁ ϖ = 0) (hx₁ : ρ₁ x = 0) (hy₂ : ρ₂ y = 0)
    (hsat₁ : ∀ g : B, e₁ (ρ₁ g) = 0 → ∃ b : B, ρ₁ g = ρ₁ y * ρ₁ b)
    (hsat₂ : ∀ g : B, e₂ (ρ₂ g) = 0 → ∃ b : B, ρ₂ g = ρ₂ x * ρ₂ b)
    (hker : ∀ g : B, ρ₁ g = 0 → ρ₂ g = 0 → ∃ b : B, g = ϖ * b) :
    (Ideal.span ({ϖ, x, y} : Set B)).IsMaximal ∧
      ∀ M : Ideal B, M.IsMaximal → M = Ideal.span ({ϖ, x, y} : Set B) := by
  have hI := span_triple_eq_ker χ ρ₁ ρ₂ e₁ e₂ ϖ x y he₁ he₂ he₂0 hϖ₁ hx₁ hy₂ hsat₁ hsat₂ hker
  have hne : Ideal.span ({ϖ, x, y} : Set B) ≠ ⊤ := by
    rw [hI, Ne, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero

  have hle : ∀ J : Ideal B, J ≠ ⊤ → J ≤ Ideal.span ({ϖ, x, y} : Set B) := by
    intro J hJ g hg
    rw [hI, RingHom.mem_ker]
    by_contra h
    exact hJ (Ideal.eq_top_of_isUnit_mem J hg (hunit g h))
  have hmax : (Ideal.span ({ϖ, x, y} : Set B)).IsMaximal := by
    refine ⟨⟨hne, fun J hJ => ?_⟩⟩
    by_contra hJtop
    exact (lt_irrefl J) (lt_of_le_of_lt (hle J hJtop) hJ)
  exact ⟨hmax, fun M hM => hM.eq_of_le hne (hle M hM.ne_top)⟩

omit [IsDomain D₁] [IsDomain D₂] in

private theorem span_pair_eq_ker_fst
    (he₁ : e₁.comp ρ₁ = χ) (he₂ : ∀ g : B, e₂ (ρ₂ g) = χ g) (_he₂0 : e₂ 0 = 0)
    (hϖ₁ : ρ₁ ϖ = 0) (hx₁ : ρ₁ x = 0)
    (hsat₂ : ∀ g : B, e₂ (ρ₂ g) = 0 → ∃ b : B, ρ₂ g = ρ₂ x * ρ₂ b)
    (hker : ∀ g : B, ρ₁ g = 0 → ρ₂ g = 0 → ∃ b : B, g = ϖ * b) :
    Ideal.span ({ϖ, x} : Set B) = RingHom.ker ρ₁ := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (rfl | rfl) <;> simpa [RingHom.mem_ker]
  · intro g hg
    rw [RingHom.mem_ker] at hg
    have hχ : χ g = 0 := by rw [← he₁, RingHom.comp_apply, hg, map_zero]
    have h2 : e₂ (ρ₂ g) = 0 := by rw [he₂, hχ]
    obtain ⟨b', hb'⟩ := hsat₂ g h2
    have hρ₁ : ρ₁ (g - x * b') = 0 := by rw [map_sub, map_mul, hg, hx₁, zero_mul, sub_zero]
    have hρ₂ : ρ₂ (g - x * b') = 0 := by rw [map_sub, map_mul, hb', sub_self]
    obtain ⟨b'', hb''⟩ := hker _ hρ₁ hρ₂
    rw [mem_span_pair_iff']
    exact ⟨b'', b', by linear_combination -hb''⟩

omit [IsDomain D₁] [IsDomain D₂] in

private theorem span_pair_eq_ker_snd
    (he₁ : e₁.comp ρ₁ = χ) (he₂ : ∀ g : B, e₂ (ρ₂ g) = χ g) (he₂0 : e₂ 0 = 0)
    (hϖ₂ : ρ₂ ϖ = 0) (hy₂ : ρ₂ y = 0)
    (hsat₁ : ∀ g : B, e₁ (ρ₁ g) = 0 → ∃ b : B, ρ₁ g = ρ₁ y * ρ₁ b)
    (hker : ∀ g : B, ρ₁ g = 0 → ρ₂ g = 0 → ∃ b : B, g = ϖ * b) :
    Ideal.span ({ϖ, y} : Set B) = RingHom.ker ρ₂ := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (rfl | rfl) <;> simpa [RingHom.mem_ker]
  · intro g hg
    rw [RingHom.mem_ker] at hg
    have hχ : χ g = 0 := by rw [← he₂, hg, he₂0]
    have h1 : e₁ (ρ₁ g) = 0 := by rw [← RingHom.comp_apply, he₁, hχ]
    obtain ⟨b, hb⟩ := hsat₁ g h1
    have hρ₁ : ρ₁ (g - y * b) = 0 := by rw [map_sub, map_mul, hb, sub_self]
    have hρ₂ : ρ₂ (g - y * b) = 0 := by rw [map_sub, map_mul, hg, hy₂, zero_mul, sub_zero]
    obtain ⟨b'', hb''⟩ := hker _ hρ₁ hρ₂
    rw [mem_span_pair_iff']
    exact ⟨b'', b, by linear_combination -hb''⟩

private theorem crossing_ideals_of_saturation
    (he₁ : e₁.comp ρ₁ = χ) (he₂ : ∀ g : B, e₂ (ρ₂ g) = χ g) (he₂0 : e₂ 0 = 0)
    (hunit : ∀ g : B, χ g ≠ 0 → IsUnit g)
    (hϖ₁ : ρ₁ ϖ = 0) (hϖ₂ : ρ₂ ϖ = 0) (hx₁ : ρ₁ x = 0) (hy₂ : ρ₂ y = 0)
    (hy₁ : ρ₁ y ≠ 0) (hx₂ : ρ₂ x ≠ 0)
    (hsat₁ : ∀ g : B, e₁ (ρ₁ g) = 0 → ∃ b : B, ρ₁ g = ρ₁ y * ρ₁ b)
    (hsat₂ : ∀ g : B, e₂ (ρ₂ g) = 0 → ∃ b : B, ρ₂ g = ρ₂ x * ρ₂ b)
    (hker : ∀ g : B, ρ₁ g = 0 → ρ₂ g = 0 → ∃ b : B, g = ϖ * b) :
    (Ideal.span ({ϖ, x, y} : Set B)).IsMaximal ∧
      (∀ M : Ideal B, M.IsMaximal → M = Ideal.span ({ϖ, x, y} : Set B)) ∧
      (Ideal.span ({ϖ, x} : Set B)).IsPrime ∧ (Ideal.span ({ϖ, y} : Set B)).IsPrime ∧
      y ∉ Ideal.span ({ϖ, x} : Set B) ∧ x ∉ Ideal.span ({ϖ, y} : Set B) := by
  obtain ⟨hmax, huniq⟩ :=
    span_triple_isMaximal_and_unique χ ρ₁ ρ₂ e₁ e₂ ϖ x y he₁ he₂ he₂0 hunit hϖ₁ hx₁ hy₂ hsat₁ hsat₂ hker
  have h1 := span_pair_eq_ker_fst χ ρ₁ ρ₂ e₁ e₂ ϖ x he₁ he₂ he₂0 hϖ₁ hx₁ hsat₂ hker
  have h2 := span_pair_eq_ker_snd χ ρ₁ ρ₂ e₁ e₂ ϖ y he₁ he₂ he₂0 hϖ₂ hy₂ hsat₁ hker
  refine ⟨hmax, huniq, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact RingHom.ker_isPrime ρ₁
  · rw [h2]; exact RingHom.ker_isPrime ρ₂
  · rw [h1, RingHom.mem_ker]; exact hy₁
  · rw [h2, RingHom.mem_ker]; exact hx₂

end RingHalf

end NodeCrossingAux

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace NodeCrossingAux

private theorem ord_pos_of_hasValue_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (h : v.HasValue f (0 : K)) (hf : f ≠ 0) : 0 < v.ord f := by

  have hres : residue v.toValuationSubring ⟨f, h.mem⟩ = 0 := by rw [h.residue_eq, map_zero]
  have hnu : ¬ IsUnit (⟨f, h.mem⟩ : v.toValuationSubring) := fun hu =>
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu hres

  have hne : v.ord f ≠ 0 := fun h0 => by
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf h0
    exact hnu hu

  by_cases hpos : 0 < v.ord f
  · exact hpos
  · exfalso
    have hneg : v.ord f < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, v.ord f = -((m : ℤ) + 1) :=
      ⟨(-v.ord f - 1).toNat, by have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -v.ord f - 1 by omega); omega⟩
    have hπF : (π : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero

    have hkey : ((u : v.toValuationSubring) : F) = f * (π : F) ^ (m + 1) := by
      rw [hu, hm, zpow_neg, mul_assoc, ← zpow_natCast, Nat.cast_succ, inv_mul_cancel₀ (zpow_ne_zero _ hπF), mul_one]

    have hdvd : π ∣ (u : v.toValuationSubring) := by
      refine ⟨⟨f, h.mem⟩ * π ^ m, Subtype.ext ?_⟩
      push_cast
      rw [hkey]; ring
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd u.isUnit)

private theorem exists_isUnit_mul_of_forall_redRestrict_eq_zero_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (ϖ ϖ' : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hϖ' : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ' * d') :
    ∃ u : ↥(NodeLocalized.coeffSubring A K), IsUnit u ∧ ϖ' = ϖ * u := by

  obtain ⟨a, ha⟩ := (hϖ ϖ').mp ((hϖ' ϖ').mpr ⟨1, (mul_one ϖ').symm⟩)
  obtain ⟨b, hb⟩ := (hϖ' ϖ).mp ((hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩)

  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have hq : NodeLocalized.redRestrict red K ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero k q
    obtain ⟨d', hd'⟩ := (hϖ _).mp hq
    rw [h0, zero_mul] at hd'
    exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hd')
  refine ⟨a, ?_, ha⟩

  have hab : ϖ * (a * b) = ϖ * 1 := by
    calc ϖ * (a * b) = (ϖ * a) * b := (mul_assoc _ _ _).symm
      _ = ϖ' * b := by rw [← ha]
      _ = ϖ := hb.symm
      _ = ϖ * 1 := (mul_one ϖ).symm
  exact IsUnit.of_mul_eq_one b (mul_left_cancel₀ hϖ0 hab)

private theorem exists_isUnit_and_natCast_eq_pow_mul_of_forall_redRestrict_eq_zero_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (ϖ ϖ' : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hϖ' : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ' * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ' ^ eK * ε) :
    ∃ ε' : ↥(NodeLocalized.coeffSubring A K), IsUnit ε' ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε' := by
  obtain ⟨u, hu, rfl⟩ := exists_isUnit_mul_of_forall_redRestrict_eq_zero_iff ϖ ϖ' hϖ hϖ'
  refine ⟨u ^ eK * ε, (hu.pow eK).mul hε, ?_⟩
  rw [hqe, mul_pow]; ring

private theorem hker_of_tuple
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) :
    ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by
  intro c
  rw [← R.redBar_residue c, map_eq_zero_iff R.redBar R.redBar.injective]
  exact IsLocalRing.residue_eq_zero_iff c

section S2
noncomputable section
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.CharPReduction ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open IsDiscreteValuationRing

section KGen

variable (M : ℕ) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private def kGen : Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (Set.range (constSeries K.toSubalgebra.toSubring) ∪
    (coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions M)

private def aGen (A₀ : Subring (AlgebraicClosure ℚ)) : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (constSeries A₀) ∪ (coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions M)

private theorem coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq) = jqNModC (AlgebraicClosure ℚ) d := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ d) = _
  exact coeffMap_jqNModC _ d

private theorem coeffEmb_mem_integralCoeffs_of_mem_divisorExpansions (A₀ : Subring (AlgebraicClosure ℚ))
    {x : LaurentSeries ℚ} (hx : x ∈ divisorExpansions M) :
    coeffEmb (AlgebraicClosure ℚ) x ∈ integralCoeffs A₀ := by
  obtain ⟨d, _, _, rfl⟩ := hx
  rw [coeffEmb_qExpand_jq]
  exact jqNModC_mem_integralCoeffs d A₀

private theorem aGen_le_integralCoeffs (A₀ : Subring (AlgebraicClosure ℚ)) : aGen M A₀ ≤ integralCoeffs A₀ := by
  rw [aGen, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact constSeries_mem_integralCoeffs A₀ a
  · exact coeffEmb_mem_integralCoeffs_of_mem_divisorExpansions M A₀ hy

private theorem fieldOver_le_kGen [NeZero M] : fieldOver M K ≤ (kGen M K) := by
  rw [fieldOver, Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
  · rcases hx with rfl | rfl
    · refine Subfield.subset_closure (Or.inr ⟨qExpand ℚ 1 jq, mem_divisorExpansions M (one_dvd M), ?_⟩)
      rw [coeffEmb_qExpand_jq, jqNModC_one]
    · refine Subfield.subset_closure (Or.inr ⟨qExpand ℚ M jq, mem_divisorExpansions M dvd_rfl, ?_⟩)
      rw [coeffEmb_qExpand_jq]

private theorem coeffEmb_mem_kGen (f : modularFunctionFieldFull M) :
    coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ) ∈ kGen M K := by
  suffices key : ∀ x : LaurentSeries ℚ, x ∈ Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M) →
      coeffEmb (AlgebraicClosure ℚ) x ∈ kGen M K from key _ f.2
  intro x hf
  induction hf using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | hx
    · refine Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) c, ?_⟩, ?_⟩)
      · exact K.algebraMap_mem c
      · show algebraMap (AlgebraicClosure ℚ) _ (algebraMap ℚ (AlgebraicClosure ℚ) c) = _
        rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
          coeffMap_single]
    · exact Subfield.subset_closure (Or.inr ⟨x, hx, rfl⟩)
  | one => simp
  | add x y _ _ hx hy => simpa using (kGen M K).add_mem hx hy
  | neg x _ hx => simpa using (kGen M K).neg_mem hx
  | inv x _ hx => simpa using (kGen M K).inv_mem hx
  | mul x y _ _ hx hy => simpa using (kGen M K).mul_mem hx hy

private def dexp (f : divisorExpansions M) : modularFunctionFieldFull M :=
  ⟨f, IntermediateField.subset_adjoin ℚ _ f.2⟩

private def kGenF [NeZero M] : Subfield (modularFunctionFieldBar M) :=
  (kGen M K).comap (modularFunctionFieldBar M).toSubfield.subtype

private theorem mem_kGenF_iff [NeZero M] (g : modularFunctionFieldBar M) :
    g ∈ kGenF M K ↔ (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ kGen M K :=
  Iff.rfl

private theorem geomAut_mem_kGenF [NeZero M] (σ : modularFunctionFieldFull M ≃ₐ[ℚ] modularFunctionFieldFull M)
    (g : modularFunctionFieldBar M) (hg : g ∈ kGenF M K) :
    geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull M) σ g ∈ kGenF M K := by

  let S : Set (modularFunctionFieldBar M) :=
    Set.range (fun c : K => algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c) ∪
      Set.range (fun f : divisorExpansions M =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((dexp M f : modularFunctionFieldFull M) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (dexp M f).2⟩ : modularFunctionFieldBar M))

  have h1 : Subfield.closure S ≤ kGenF M K := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨f, rfl⟩)
    · show ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c : modularFunctionFieldBar M) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ kGen M K
      exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨f, f.2, rfl⟩)

  have h2 : kGenF M K ≤ Subfield.closure S := by
    intro x hx
    have hmap : kGen M K ≤ (Subfield.closure S).map (modularFunctionFieldBar M).toSubfield.subtype := by
      rw [kGen, Subfield.closure_le]
      rintro y (⟨c, rfl⟩ | ⟨f, hf, rfl⟩)
      · exact ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c,
          Subfield.subset_closure (Or.inl ⟨c, rfl⟩), rfl⟩
      · exact ⟨_, Subfield.subset_closure (Or.inr ⟨⟨f, hf⟩, rfl⟩), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hmap hx
    rwa [← Subtype.coe_injective hyx]

  have h3 : ∀ x ∈ Subfield.closure S,
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull M) σ x ∈ Subfield.closure S := by
    intro x hx
    induction hx using Subfield.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨f, rfl⟩
      · rw [AlgEquiv.commutes]
        exact Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
      · show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull M) σ
            ⟨coeffEmb (AlgebraicClosure ℚ) ((dexp M f : modularFunctionFieldFull M) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (dexp M f).2⟩ ∈ Subfield.closure S
        rw [geomAut_coeffEmb]
        exact h2 (coeffEmb_mem_kGen M K (σ (dexp M f)))
    | one => simp
    | add x y _ _ hx hy => simpa using (Subfield.closure S).add_mem hx hy
    | neg x _ hx => simpa using (Subfield.closure S).neg_mem hx
    | inv x _ hx => simpa using (Subfield.closure S).inv_mem hx
    | mul x y _ _ hx hy => simpa using (Subfield.closure S).mul_mem hx hy
  exact h1 (h3 g (h2 hg))

end KGen

section Disc

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : PlaceSpecialization.ProlongationTuple P)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private theorem isUnit_iff_inv_mem {F S : Type*} [Field F] [SetLike S F] [SubringClass S F] (s : S) (x : s) :
    IsUnit x ↔ (x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ s := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : s) : F) * ((u⁻¹ : sˣ) : s) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact ((u⁻¹ : sˣ) : s).2
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

variable {K} in
include q in

private theorem coeffSubring_ne [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    coeffSubring A K ≠ K.toSubalgebra.toSubring := by
  intro h
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
    have hK : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem (natCast_mem K q)
    rw [h]
    exact hK
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hunit : IsUnit (⟨(q : AlgebraicClosure ℚ), hqA⟩ : A) :=
    (isUnit_iff_inv_mem A _).mpr ⟨hq0, hmem.1⟩
  have hred : red ⟨(q : AlgebraicClosure ℚ), hqA⟩ = 0 := by
    have : (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : A) = (q : A) := Subtype.ext (by simp)
    rw [this, map_natCast, CharP.cast_eq_zero]
  exact (IsLocalRing.mem_maximalIdeal _).mp ((hker _).mp hred) hunit

include q in

private theorem isDiscreteValuationRing_coeffSubring [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) :
    IsDiscreteValuationRing (coeffSubring A K) :=
  (coeffSubring_eq_or_isDiscreteValuationRing A K).resolve_left (coeffSubring_ne (q := q) hker)

private theorem maximalIdeal_coeffSubring_eq [IsDiscreteValuationRing (coeffSubring A K)]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    IsLocalRing.maximalIdeal (coeffSubring A K) = Ideal.span {ϖ} := by
  ext d
  have hA : IsUnit d ↔ IsUnit (⟨(d : AlgebraicClosure ℚ), d.2.1⟩ : A) := by
    rw [isUnit_iff_inv_mem (coeffSubring A K) d, isUnit_iff_inv_mem A]
    exact ⟨fun h => ⟨h.1, h.2.1⟩,
      fun h => ⟨h.1, h.2, (show (d : AlgebraicClosure ℚ)⁻¹ ∈ K from inv_mem d.2.2)⟩⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hA, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal, ← hker ⟨(d : AlgebraicClosure ℚ), d.2.1⟩, Ideal.mem_span_singleton']
  exact (hϖ d).trans ⟨fun ⟨d', h⟩ => ⟨d', by rw [h, mul_comm]⟩, fun ⟨d', h⟩ => ⟨d', by rw [← h, mul_comm]⟩⟩

private theorem irreducible_varpi [IsDiscreteValuationRing (coeffSubring A K)]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    Irreducible ϖ :=
  (irreducible_iff_uniformizer ϖ).mpr (maximalIdeal_coeffSubring_eq K hker ϖ hϖ)

include q in

private theorem exists_pow_mul_mem_coeffSubring [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (c : AlgebraicClosure ℚ) (hc : c ∈ K) :
    ∃ m : ℕ, (ϖ : AlgebraicClosure ℚ) ^ m * c ∈ coeffSubring A K := by
  haveI := isDiscreteValuationRing_coeffSubring (q := q) K hker
  have hirr := irreducible_varpi K hker ϖ hϖ
  rcases ValuationSubring.mem_or_inv_mem A c with hcA | hcA
  · exact ⟨0, by rw [pow_zero, one_mul]; exact ⟨hcA, hc⟩⟩
  · by_cases hc0 : c = 0
    · exact ⟨0, by rw [hc0, mul_zero]; exact zero_mem _⟩
    set d : coeffSubring A K := ⟨c⁻¹, ⟨hcA, (show c⁻¹ ∈ K from inv_mem hc)⟩⟩ with hd
    have hd0 : d ≠ 0 := fun h => inv_ne_zero hc0 (congrArg Subtype.val h)
    obtain ⟨e, u, hu⟩ := eq_unit_mul_pow_irreducible hd0 hirr
    refine ⟨e, ?_⟩
    have h1 : ((u : coeffSubring A K) : AlgebraicClosure ℚ) *
        ((u⁻¹ : (coeffSubring A K)ˣ) : coeffSubring A K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hϖ0 : ((ϖ : coeffSubring A K) : AlgebraicClosure ℚ) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
    have hval : (c⁻¹ : AlgebraicClosure ℚ) = (u : coeffSubring A K) * (ϖ : AlgebraicClosure ℚ) ^ e := by
      have := congrArg Subtype.val hu
      simpa [hd] using this
    have key : (ϖ : AlgebraicClosure ℚ) ^ e * c = ((u⁻¹ : (coeffSubring A K)ˣ) : coeffSubring A K) := by
      rw [← inv_eq_of_mul_eq_one_right h1]
      have hu' : ((u : coeffSubring A K) : AlgebraicClosure ℚ) = c⁻¹ * ((ϖ : AlgebraicClosure ℚ) ^ e)⁻¹ := by
        rw [hval, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), mul_one]
      rw [hu', mul_inv, inv_inv, inv_inv, mul_comm]
    rw [key]
    exact SetLike.coe_mem _

omit [NeZero N] in

private theorem exists_pow_mul_mem_aGen [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {t : LaurentSeries (AlgebraicClosure ℚ)}
    (ht : t ∈ Subring.closure (Set.range (constSeries K.toSubalgebra.toSubring) ∪
      (coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions (N * q))) :
    ∃ m : ℕ, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) ^ m * t
      ∈ aGen (N * q) (coeffSubring A K) := by
  set Pϖ := algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) with hP
  have hPmem : Pϖ ∈ aGen (N * q) (coeffSubring A K) := Subring.subset_closure (Or.inl ⟨ϖ, rfl⟩)
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
    · obtain ⟨m, hm⟩ := exists_pow_mul_mem_coeffSubring (q := q) K hker ϖ hϖ (c : AlgebraicClosure ℚ) c.2
      refine ⟨m, ?_⟩
      have : Pϖ ^ m * constSeries K.toSubalgebra.toSubring c =
          constSeries (coeffSubring A K) ⟨_, hm⟩ := by
        show Pϖ ^ m * algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) =
          algebraMap (AlgebraicClosure ℚ) _ ((ϖ : AlgebraicClosure ℚ) ^ m * c)
        rw [map_mul, map_pow]
      rw [this]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)⟩
  | zero => exact ⟨0, by rw [mul_zero]; exact zero_mem _⟩
  | one => exact ⟨0, by rw [pow_zero, one_mul]; exact one_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    have : Pϖ ^ (m₁ + m₂) * (x + y) = Pϖ ^ m₂ * (Pϖ ^ m₁ * x) + Pϖ ^ m₁ * (Pϖ ^ m₂ * y) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hPmem _) h₁) (mul_mem (pow_mem hPmem _) h₂)
  | neg x _ hx =>
    obtain ⟨m, h⟩ := hx
    exact ⟨m, by rw [mul_neg]; exact neg_mem h⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    have : Pϖ ^ (m₁ + m₂) * (x * y) = (Pϖ ^ m₁ * x) * (Pϖ ^ m₂ * y) := by ring
    rw [this]
    exact mul_mem h₁ h₂

private theorem exists_pow_mul_coeffMap {A₀ : Subring (AlgebraicClosure ℚ)} [IsDiscreteValuationRing A₀]
    (ϖ : A₀) (hirr : Irreducible ϖ) {t : LaurentSeries (AlgebraicClosure ℚ)}
    (ht : t ∈ integralCoeffs A₀) (ht0 : t ≠ 0) :
    ∃ (m : ℕ) (y : LaurentSeries A₀),
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) ^ m *
          coeffMap A₀.subtype y = t ∧ ∃ n : ℤ, IsUnit (y.coeff n) := by
  classical
  let c : ℤ → A₀ := fun n => ⟨t.coeff n, ht n⟩
  have hc : ∀ n, (c n : AlgebraicClosure ℚ) = t.coeff n := fun n => rfl
  have H : ∀ n, c n ≠ 0 → ∃ e : ℕ, ∃ u : A₀ˣ, c n = u * ϖ ^ e := fun n hn =>
    eq_unit_mul_pow_irreducible hn hirr
  choose e u heu using H
  obtain ⟨n₀, hn₀⟩ : ∃ n, c n ≠ 0 := by
    by_contra hall
    apply ht0
    ext n
    have h0 : c n = 0 := not_not.mp (not_exists.mp hall n)
    rw [← hc, h0]
    rfl
  have hex : ∃ m : ℕ, ∃ n, ∃ h : c n ≠ 0, e n h = m := ⟨_, n₀, hn₀, rfl⟩
  obtain ⟨n₁, hn₁, hm₁⟩ : ∃ n, ∃ h : c n ≠ 0, e n h = Nat.find hex := Nat.find_spec hex
  have hmin : ∀ n (h : c n ≠ 0), Nat.find hex ≤ e n h := fun n h => Nat.find_min' hex ⟨n, h, rfl⟩
  set m := Nat.find hex with hm
  have hdvd : ∀ n, ϖ ^ m ∣ c n := by
    intro n
    by_cases h : c n = 0
    · rw [h]; exact dvd_zero _
    · rw [heu n h]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (hmin n h)) _
  choose d hd using hdvd
  have hϖ0 : (ϖ : A₀) ≠ 0 := hirr.ne_zero
  have hsupp : (Function.support d).IsPWO := by
    refine t.isPWO_support.mono ?_
    intro n hn
    rw [Function.mem_support] at hn
    rw [HahnSeries.mem_support, ← hc]
    intro h0
    apply hn
    have h1 : ϖ ^ m * d n = 0 := by rw [← hd n]; exact Subtype.ext h0
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hϖ0)
  let y : LaurentSeries A₀ := ⟨d, hsupp⟩
  have hy : ∀ n, y.coeff n = d n := fun n => rfl
  refine ⟨m, y, ?_, n₁, ?_⟩
  · ext n
    rw [← map_pow, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul,
      HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, hy, ← hc, hd n, Subring.coe_mul, Subring.coe_pow]
    rfl
  · have h1 : ϖ ^ m * d n₁ = ϖ ^ m * (u n₁ hn₁ : A₀) := by rw [← hd n₁, heu n₁ hn₁, hm₁, mul_comm]
    rw [hy, mul_left_cancel₀ (pow_ne_zero _ hϖ0) h1]
    exact Units.isUnit _

private def inclCoeff : coeffSubring A K →+* A where
  toFun d := ⟨d, d.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Fact q.Prime] [NeZero N] in

private theorem closure_le_bar :
    Subring.closure (Set.range (constSeries K.toSubalgebra.toSubring) ∪
      (coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions (N * q)) ≤
      (modularFunctionFieldBar (N * q)).toSubring := by
  rw [Subring.closure_le]
  rintro x (⟨c, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact (modularFunctionFieldBar (N * q)).algebraMap_mem (c : AlgebraicClosure ℚ)
  · exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (IntermediateField.subset_adjoin ℚ _ hy)

private theorem isUnit_fst_of_coeffMap (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q)) {n : ℤ} (hn : IsUnit (y.coeff n)) :
    ∃ h : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers,
      IsUnit (⟨⟨coeffMap A.subtype y, hy⟩, h⟩ : R.R₁.integers) := by
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hy
  refine ⟨h, R.R₁.isUnit_of_residue_ne_zero ?_⟩
  intro h0
  have h0' : coeffMap (IsLocalRing.residue A) y = 0 := by
    rw [← hres, h0]
    rfl
  have : (coeffMap (IsLocalRing.residue A) y).coeff n = 0 := by rw [h0']; rfl
  rw [coeffMap_coeff] at this
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hn this

private theorem exists_pow_mul_of_mem_kGen_fst [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (g : modularFunctionFieldBar (N * q)) (hg0 : g ≠ 0) (hg : g ∈ kGenF (N * q) K) :
    ∃ (n₁ n₂ : ℕ) (u : R.R₁.integers), IsUnit u ∧
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ n₂ * g =
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ n₁ *
          (u : modularFunctionFieldBar (N * q)) := by
  haveI := isDiscreteValuationRing_coeffSubring (q := q) K hker
  have hirr := irreducible_varpi K hker ϖ hϖ
  set Pϖ := algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ)
    with hPϖ
  set ϖF := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
    with hϖF
  have hϖ0 : ((ϖ : coeffSubring A K) : AlgebraicClosure ℚ) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hP0 : Pϖ ≠ 0 := (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) _).injective).mpr hϖ0
  have hcoeP : ∀ n : ℕ, ((ϖF ^ n : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) =
      Pϖ ^ n := fun n => by
    rw [SubmonoidClass.coe_pow]; rfl

  obtain ⟨r, hr, s, hs, hrs⟩ := Subfield.mem_closure_iff.mp hg
  have hg0' : (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : r / 0 = (g : LaurentSeries (AlgebraicClosure ℚ)) := hrs
    rw [div_zero] at this; exact hg0' this.symm
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : 0 / s = (g : LaurentSeries (AlgebraicClosure ℚ)) := hrs
    rw [zero_div] at this; exact hg0' this.symm
  have hrs' : r / s = (g : LaurentSeries (AlgebraicClosure ℚ)) := hrs
  have hgs : (g : LaurentSeries (AlgebraicClosure ℚ)) * s = r := by rw [← hrs', div_mul_cancel₀ _ hs0]

  obtain ⟨a, ha⟩ := exists_pow_mul_mem_aGen (q := q) K hker ϖ hϖ hr
  obtain ⟨b, hb⟩ := exists_pow_mul_mem_aGen (q := q) K hker ϖ hϖ hs

  obtain ⟨mr, yr, hyr, nr, hur⟩ := exists_pow_mul_coeffMap ϖ hirr
    (aGen_le_integralCoeffs _ _ ha) (mul_ne_zero (pow_ne_zero _ hP0) hr0)
  obtain ⟨ms, ys, hys, ns, hus⟩ := exists_pow_mul_coeffMap ϖ hirr
    (aGen_le_integralCoeffs _ _ hb) (mul_ne_zero (pow_ne_zero _ hP0) hs0)

  set yr' : LaurentSeries A := coeffMap (inclCoeff (A := A) K) yr with hyr'
  set ys' : LaurentSeries A := coeffMap (inclCoeff (A := A) K) ys with hys'
  have hcr : coeffMap A.subtype yr' = coeffMap (coeffSubring A K).subtype yr := by
    rw [hyr', coeffMap_coeffMap]; rfl
  have hcs : coeffMap A.subtype ys' = coeffMap (coeffSubring A K).subtype ys := by
    rw [hys', coeffMap_coeffMap]; rfl

  have hPbar : Pϖ ∈ modularFunctionFieldBar (N * q) := (modularFunctionFieldBar (N * q)).algebraMap_mem _
  have hrbar : r ∈ modularFunctionFieldBar (N * q) := closure_le_bar (N := N) (q := q) K hr
  have hsbar : s ∈ modularFunctionFieldBar (N * q) := closure_le_bar (N := N) (q := q) K hs
  have hur_eq : coeffMap (coeffSubring A K).subtype yr = (Pϖ ^ mr)⁻¹ * (Pϖ ^ a * r) := by
    rw [← hyr, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hP0), one_mul]
  have hus_eq : coeffMap (coeffSubring A K).subtype ys = (Pϖ ^ ms)⁻¹ * (Pϖ ^ b * s) := by
    rw [← hys, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hP0), one_mul]
  have hyr_bar : coeffMap A.subtype yr' ∈ modularFunctionFieldBar (N * q) := by
    rw [hcr, hur_eq]
    exact mul_mem (inv_mem (pow_mem hPbar _)) (mul_mem (pow_mem hPbar _) hrbar)
  have hys_bar : coeffMap A.subtype ys' ∈ modularFunctionFieldBar (N * q) := by
    rw [hcs, hus_eq]
    exact mul_mem (inv_mem (pow_mem hPbar _)) (mul_mem (pow_mem hPbar _) hsbar)

  have hnr : IsUnit (yr'.coeff nr) := by
    rw [hyr', coeffMap_coeff]; exact hur.map _
  have hns : IsUnit (ys'.coeff ns) := by
    rw [hys', coeffMap_coeff]; exact hus.map _
  obtain ⟨hR, huR⟩ := isUnit_fst_of_coeffMap R yr' hyr_bar hnr
  obtain ⟨hS, huS⟩ := isUnit_fst_of_coeffMap R ys' hys_bar hns
  set uR : R.R₁.integers := ⟨⟨coeffMap A.subtype yr', hyr_bar⟩, hR⟩ with huR'
  set uS : R.R₁.integers := ⟨⟨coeffMap A.subtype ys', hys_bar⟩, hS⟩ with huS'

  have key : Pϖ ^ (a + ms) * (g : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype ys' =
      Pϖ ^ (mr + b) * coeffMap A.subtype yr' := by
    rw [hcr, hcs]
    linear_combination (Pϖ ^ a * (g : LaurentSeries (AlgebraicClosure ℚ))) * hys +
      Pϖ ^ (a + b) * hgs + (-(Pϖ ^ b)) * hyr
  have keyF : ϖF ^ (a + ms) * g * (uS : modularFunctionFieldBar (N * q)) =
      ϖF ^ (mr + b) * (uR : modularFunctionFieldBar (N * q)) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, hcoeP, hcoeP]
    exact key

  set uSi : R.R₁.integers := ((huS.unit⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) with huSi
  have hinv : uS * uSi = 1 := by rw [huSi]; exact huS.mul_val_inv
  have hinvF : (uS : modularFunctionFieldBar (N * q)) * (uSi : modularFunctionFieldBar (N * q)) = 1 := by
    rw [← MulMemClass.coe_mul, hinv]; rfl
  refine ⟨mr + b, a + ms, uR * uSi, huR.mul (Units.isUnit _), ?_⟩
  rw [MulMemClass.coe_mul]
  calc ϖF ^ (a + ms) * g
      = ϖF ^ (a + ms) * g * ((uS : modularFunctionFieldBar (N * q)) * (uSi : modularFunctionFieldBar (N * q))) := by
        rw [hinvF, mul_one]
    _ = ϖF ^ (a + ms) * g * (uS : modularFunctionFieldBar (N * q)) * (uSi : modularFunctionFieldBar (N * q)) := by
        ring
    _ = ϖF ^ (mr + b) * (uR : modularFunctionFieldBar (N * q)) * (uSi : modularFunctionFieldBar (N * q)) := by
        rw [keyF]
    _ = ϖF ^ (mr + b) * ((uR : modularFunctionFieldBar (N * q)) * (uSi : modularFunctionFieldBar (N * q))) := by
        ring

private theorem exists_pow_mul_of_mem_kGen_snd [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (g : modularFunctionFieldBar (N * q)) (hg0 : g ≠ 0) (hg : g ∈ kGenF (N * q) K) :
    ∃ (n₁ n₂ : ℕ) (u : R.R₂.integers), IsUnit u ∧
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ n₂ * g =
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ) ^ n₁ *
          (u : modularFunctionFieldBar (N * q)) := by
  set ϖF := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
    with hϖF
  set α := atkinLehnerBar N q with hα

  have hαg : α g ∈ kGenF (N * q) K := geomAut_mem_kGenF (N * q) K (atkinLehnerInvolutionFull N q) g hg
  have hαg0 : α g ≠ 0 := (map_ne_zero_iff α α.injective).mpr hg0
  obtain ⟨n₁, n₂, u₁, hu₁, hEq⟩ := exists_pow_mul_of_mem_kGen_fst R K hker ϖ hϖ (α g) hαg0 hαg

  have hmem : ∀ x : R.R₁.integers, α.symm (x : modularFunctionFieldBar (N * q)) ∈ R.R₂.integers := by
    intro x
    rw [R.mem_integersSnd_iff]
    have : atkinLehnerBar N q (α.symm (x : modularFunctionFieldBar (N * q))) = x := by
      rw [hα, AlgEquiv.apply_symm_apply]
    rw [this]
    exact (R.mem_integersFst_iff _).mp x.2
  obtain ⟨v₁, hv₁⟩ := hu₁.exists_right_inv
  set u₂ : R.R₂.integers := ⟨α.symm (u₁ : modularFunctionFieldBar (N * q)), hmem u₁⟩ with hu₂
  set v₂ : R.R₂.integers := ⟨α.symm (v₁ : modularFunctionFieldBar (N * q)), hmem v₁⟩ with hv₂
  have hu₂unit : IsUnit u₂ := by
    refine IsUnit.of_mul_eq_one v₂ (Subtype.ext ?_)
    show α.symm (u₁ : modularFunctionFieldBar (N * q)) * α.symm (v₁ : modularFunctionFieldBar (N * q)) = 1
    rw [← map_mul, ← MulMemClass.coe_mul, hv₁]
    simp
  refine ⟨n₁, n₂, u₂, hu₂unit, ?_⟩
  apply α.injective
  rw [map_mul, map_pow, map_mul, map_pow, AlgEquiv.commutes]
  show ϖF ^ n₂ * α g = ϖF ^ n₁ * α (α.symm (u₁ : modularFunctionFieldBar (N * q)))
  rw [AlgEquiv.apply_symm_apply]
  exact hEq

private theorem exists_eq_nodeConst_mul_of_nodeResidue_eq_zero [FiniteDimensional ℚ K]
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (w : Place k (modularFunctionFieldC k N))
    (ϖ : coeffSubring A K)
    (hϖ : ∀ d : coeffSubring A K, redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (g : R.nodeIntegersOver K w)
    (h₁ : R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0) (h₂ : R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) :
    ∃ b : R.nodeIntegersOver K w, g = R.nodeConst K w ϖ * b := by
  haveI := isDiscreteValuationRing_coeffSubring (q := q) K hker
  have hirr := irreducible_varpi K hker ϖ hϖ
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [hg0, mul_zero]⟩
  set ϖF := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (ϖ : AlgebraicClosure ℚ)
    with hϖF
  have hϖ0 : ((ϖ : coeffSubring A K) : AlgebraicClosure ℚ) ≠ 0 := fun h => hirr.ne_zero (Subtype.ext h)
  have hϖF0 : ϖF ≠ 0 := (map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) _).injective).mpr hϖ0

  have hϖA : (⟨(ϖ : AlgebraicClosure ℚ), ϖ.2.1⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hker]
    exact (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hg0' : ((g : R.nodeIntegersOver K w) : modularFunctionFieldBar (N * q)) ≠ 0 := fun h => hg0 (Subtype.ext h)
  have hgK : ((g : R.nodeIntegersOver K w) : modularFunctionFieldBar (N * q)) ∈ kGenF (N * q) K :=
    fieldOver_le_kGen (N * q) K g.2.2

  set bF : modularFunctionFieldBar (N * q) := ϖF⁻¹ * (g : modularFunctionFieldBar (N * q)) with hbF
  have hgb : (g : modularFunctionFieldBar (N * q)) = ϖF * bF := by rw [hbF, mul_inv_cancel_left₀ hϖF0]

  have hb₁ : bF ∈ R.R₁.integers := by
    obtain ⟨n₁, n₂, u, hu, hEq⟩ := exists_pow_mul_of_mem_kGen_fst R K hker ϖ hϖ _ hg0' hgK
    rw [← hϖF] at hEq
    have hϖR : ϖF ∈ R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr ϖ.2.1
    have hgR : (⟨(g : modularFunctionFieldBar (N * q)), g.2.1.1⟩ : R.R₁.integers) ∈
        IsLocalRing.maximalIdeal R.R₁.integers := by
      rw [← R.R₁.ker_residue, RingHom.mem_ker]
      have h₁' : R.ι (R.R₁.residue ⟨(g : modularFunctionFieldBar (N * q)), g.2.1.1⟩) = 0 := h₁
      exact (map_eq_zero_iff _ R.ι.injective).mp h₁'

    have hlt : n₂ < n₁ := by
      by_contra hle
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hle)
      apply (IsLocalRing.mem_maximalIdeal _).mp ?_ hu
      have hu_eq : u = (⟨ϖF, hϖR⟩ : R.R₁.integers) ^ d *
          ⟨(g : modularFunctionFieldBar (N * q)), g.2.1.1⟩ := by
        apply Subtype.ext
        show (u : modularFunctionFieldBar (N * q)) = ϖF ^ d * (g : modularFunctionFieldBar (N * q))
        have := hEq
        rw [pow_add, mul_assoc] at this
        exact (mul_left_cancel₀ (pow_ne_zero _ hϖF0) this).symm
      rw [hu_eq]
      exact Ideal.mul_mem_left _ _ hgR
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hb_eq : bF = ϖF ^ d * (u : modularFunctionFieldBar (N * q)) := by
      rw [hbF]
      have := hEq
      rw [show n₂ + d + 1 = n₂ + (d + 1) from by ring, pow_add, mul_assoc] at this
      have h2 := mul_left_cancel₀ (pow_ne_zero _ hϖF0) this
      rw [h2, pow_succ', mul_assoc, inv_mul_cancel_left₀ hϖF0]
    rw [hb_eq]
    exact mul_mem (pow_mem hϖR _) u.2

  have hb₂ : bF ∈ R.R₂.integers := by
    obtain ⟨n₁, n₂, u, hu, hEq⟩ := exists_pow_mul_of_mem_kGen_snd R K hker ϖ hϖ _ hg0' hgK
    rw [← hϖF] at hEq
    have hϖR : ϖF ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr ϖ.2.1
    have hgR : (⟨(g : modularFunctionFieldBar (N * q)), g.2.1.2.1⟩ : R.R₂.integers) ∈
        IsLocalRing.maximalIdeal R.R₂.integers := by
      rw [← R.R₂.ker_residue, RingHom.mem_ker]
      have h₂' : R.ι (R.R₂.residue ⟨(g : modularFunctionFieldBar (N * q)), g.2.1.2.1⟩) = 0 := h₂
      exact (map_eq_zero_iff _ R.ι.injective).mp h₂'
    have hlt : n₂ < n₁ := by
      by_contra hle
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hle)
      apply (IsLocalRing.mem_maximalIdeal _).mp ?_ hu
      have hu_eq : u = (⟨ϖF, hϖR⟩ : R.R₂.integers) ^ d *
          ⟨(g : modularFunctionFieldBar (N * q)), g.2.1.2.1⟩ := by
        apply Subtype.ext
        show (u : modularFunctionFieldBar (N * q)) = ϖF ^ d * (g : modularFunctionFieldBar (N * q))
        have := hEq
        rw [pow_add, mul_assoc] at this
        exact (mul_left_cancel₀ (pow_ne_zero _ hϖF0) this).symm
      rw [hu_eq]
      exact Ideal.mul_mem_left _ _ hgR
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hb_eq : bF = ϖF ^ d * (u : modularFunctionFieldBar (N * q)) := by
      rw [hbF]
      have := hEq
      rw [show n₂ + d + 1 = n₂ + (d + 1) from by ring, pow_add, mul_assoc] at this
      have h2 := mul_left_cancel₀ (pow_ne_zero _ hϖF0) this
      rw [h2, pow_succ', mul_assoc, inv_mul_cancel_left₀ hϖF0]
    rw [hb_eq]
    exact mul_mem (pow_mem hϖR _) u.2

  have hbV : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      bF ∈ V.toValuationSubring := by
    intro V hV
    refine mul_mem ?_ (g.2.1.2.2 V hV)
    rw [hϖF, ← map_inv₀]
    exact V.algebraMap_mem' _

  have hbK : (bF : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (N * q) K := by
    rw [hbF, MulMemClass.coe_mul]
    refine mul_mem ?_ g.2.2
    rw [hϖF, ← map_inv₀]
    exact Subfield.subset_closure (Or.inl ⟨⟨_, (show ((ϖ : coeffSubring A K) : AlgebraicClosure ℚ)⁻¹ ∈ K
      from inv_mem ϖ.2.2)⟩, rfl⟩)
  refine ⟨⟨bF, ⟨hb₁, hb₂, hbV⟩, hbK⟩, Subtype.ext ?_⟩
  rw [MulMemClass.coe_mul, coe_nodeConst]
  exact hgb

end Disc

end
end S2

section G
noncomputable section
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

private theorem inv_mem_of_isUnit {F S : Type*} [Field F] [SetLike S F] [SubringClass S F] {s : S} {x : F}
    (hx : x ∈ s) (hu : IsUnit (⟨x, hx⟩ : s)) : x⁻¹ ∈ s := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u : s) : F) * ((u⁻¹ : sˣ) : s) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu] at h1
  rw [inv_eq_of_mul_eq_one_right h1]
  exact ((u⁻¹ : sˣ) : s).2

section RingHalfData

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem isRational_of_place_bar (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    V.IsRational :=
  (Place.isRational_iff_deg_eq_one V).mpr (deg_eq_one_modularFunctionFieldBar (N * q) V)

omit [IsAlgClosed k] [DecidableEq k] in

private theorem exists_reduceFst_eq (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place k ↥(modularFunctionFieldC k N)) :
    ∃ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w := by
  obtain ⟨v, hv⟩ := P.d4 w
  haveI : CharZero ↥(modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).injective
  obtain ⟨V, hV⟩ := Place.restrictAlong_surjective (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
    (separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) v
  refine ⟨V, ?_⟩
  show P.sp (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w
  dsimp only at hV
  rw [hV, hv]

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : PlaceSpecialization.ProlongationTuple P)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k ↥(modularFunctionFieldC k N))

private theorem exists_ringHalfData (hw : w ∈ ssPlaces q N k)
    (hsp₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsp₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩)) :
    ∃ (ρ₁ : ↥(R.nodeIntegersOver K w) →+* ↥w.toValuationSubring)
      (ρ₂ : ↥(R.nodeIntegersOver K w) →+* ↥(arithFrobC q k N • w).toValuationSubring)
      (e₁ : ↥w.toValuationSubring →+* k) (e₂ : ↥(arithFrobC q k N • w).toValuationSubring → k),
      (∀ g, e₂ (ρ₂ g) = e₁ (ρ₁ g)) ∧ e₂ 0 = 0 ∧
      (∀ g, e₁ (ρ₁ g) ≠ 0 → IsUnit g) ∧
      (∀ g, ((ρ₁ g : ↥w.toValuationSubring) : ↥(modularFunctionFieldC k N)) = R.nodeResidue₁ w ⟨g, g.2.1⟩) ∧
      (∀ g, ((ρ₂ g : ↥(arithFrobC q k N • w).toValuationSubring) : ↥(modularFunctionFieldC k N)) =
        R.nodeResidue₂ w ⟨g, g.2.1⟩) ∧
      (∀ (f : ↥w.toValuationSubring) (a : k), w.HasValue (f : ↥(modularFunctionFieldC k N)) a ↔ e₁ f = a) ∧
      (∀ (g : ↥(R.nodeIntegersOver K w)) (a : k),
        (arithFrobC q k N • w).HasValue
          ((ρ₂ g : ↥(arithFrobC q k N • w).toValuationSubring) : ↥(modularFunctionFieldC k N)) a ↔
        e₂ (ρ₂ g) = a) := by
  classical
  obtain ⟨V₀, hV₀⟩ := exists_reduceFst_eq P w

  have hval : ∀ g : ↥(R.nodeIntegersOver K w), ∃ c : AlgebraicClosure ℚ,
      V₀.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c := fun g => by
    obtain ⟨c, hc, -⟩ := V₀.exists_hasValue_of_surjective (isRational_of_place_bar V₀) (g.2.1.2.2 V₀ hV₀)
    exact ⟨c, hc⟩

  have hmem₁ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ ∈ w.toValuationSubring := by
    intro g
    obtain ⟨c, hc⟩ := hval g
    obtain ⟨hcA, h⟩ := hsp₁ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    exact h.mem
  have hmem₂ : ∀ g : ↥(R.nodeIntegersOver K w),
      R.nodeResidue₂ w ⟨g, g.2.1⟩ ∈ (arithFrobC q k N • w).toValuationSubring := by
    intro g
    obtain ⟨c, hc⟩ := hval g
    obtain ⟨hcA, h⟩ := hsp₂ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    exact h.mem
  let incl : ↥(R.nodeIntegersOver K w) →+* ↥(R.nodeIntegers w) := Subring.inclusion (fun f hf => hf.1)
  let ρ₁ : ↥(R.nodeIntegersOver K w) →+* ↥w.toValuationSubring :=
    ((R.nodeResidue₁ w).comp incl).codRestrict w.toValuationSubring hmem₁
  let ρ₂ : ↥(R.nodeIntegersOver K w) →+* ↥(arithFrobC q k N • w).toValuationSubring :=
    ((R.nodeResidue₂ w).comp incl).codRestrict (arithFrobC q k N • w).toValuationSubring hmem₂
  have hρ₁ : ∀ g, ((ρ₁ g : ↥w.toValuationSubring) : ↥(modularFunctionFieldC k N)) = R.nodeResidue₁ w ⟨g, g.2.1⟩ :=
    fun g => rfl
  have hρ₂ : ∀ g, ((ρ₂ g : ↥(arithFrobC q k N • w).toValuationSubring) : ↥(modularFunctionFieldC k N)) =
      R.nodeResidue₂ w ⟨g, g.2.1⟩ := fun g => rfl

  have hw1 : w.IsRational := hw.1
  let E : k ≃+* w.ResidueField :=
    RingEquiv.ofBijective (algebraMap k w.ResidueField) ⟨w.algebraMap_residueField_injective, hw1⟩
  let e₁ : ↥w.toValuationSubring →+* k := E.symm.toRingHom.comp (residue ↥w.toValuationSubring)
  have he₁ : ∀ (f : ↥w.toValuationSubring) (a : k),
      w.HasValue (f : ↥(modularFunctionFieldC k N)) a ↔ e₁ f = a := by
    intro f a
    have hf : (⟨(f : ↥(modularFunctionFieldC k N)), f.2⟩ : ↥w.toValuationSubring) = f := Subtype.ext rfl
    constructor
    · rintro ⟨hf', h⟩
      have hf'' : (⟨(f : ↥(modularFunctionFieldC k N)), hf'⟩ : ↥w.toValuationSubring) = f := Subtype.ext rfl
      rw [hf''] at h
      show E.symm (residue ↥w.toValuationSubring f) = a
      rw [h, show algebraMap k w.ResidueField a = E a from rfl, RingEquiv.symm_apply_apply]
    · intro h
      refine ⟨f.2, ?_⟩
      rw [hf]
      have h' : E.symm (residue ↥w.toValuationSubring f) = a := h
      rw [RingEquiv.symm_apply_eq] at h'
      rw [h']
      rfl

  let e₂ : ↥(arithFrobC q k N • w).toValuationSubring → k :=
    fun f => (arithFrobC q k N • w).residueInv (residue ↥(arithFrobC q k N • w).toValuationSubring f)
  have he₂0 : e₂ 0 = 0 := by
    show (arithFrobC q k N • w).residueInv (residue _ 0) = 0
    rw [map_zero, ← map_zero (algebraMap k (arithFrobC q k N • w).ResidueField), Place.residueInv_algebraMap]
  have he₂val : ∀ (f : ↥(arithFrobC q k N • w).toValuationSubring) (a : k),
      (arithFrobC q k N • w).HasValue (f : ↥(modularFunctionFieldC k N)) a → e₂ f = a := by
    rintro f a ⟨hf', h⟩
    have hf'' : (⟨(f : ↥(modularFunctionFieldC k N)), hf'⟩ : ↥(arithFrobC q k N • w).toValuationSubring) = f :=
      Subtype.ext rfl
    rw [hf''] at h
    show (arithFrobC q k N • w).residueInv (residue _ f) = a
    rw [h, Place.residueInv_algebraMap]

  have hagree : ∀ g, e₂ (ρ₂ g) = e₁ (ρ₁ g) := by
    intro g
    obtain ⟨c, hc⟩ := hval g
    obtain ⟨hcA, h₁⟩ := hsp₁ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    obtain ⟨hcA', h₂⟩ := hsp₂ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    have e1 : e₁ (ρ₁ g) = red ⟨c, hcA⟩ := (he₁ (ρ₁ g) (red ⟨c, hcA⟩)).mp h₁
    have e2 : e₂ (ρ₂ g) = red ⟨c, hcA'⟩ := he₂val (ρ₂ g) (red ⟨c, hcA'⟩) h₂
    rw [e1, e2]

  have hunit : ∀ g, e₁ (ρ₁ g) ≠ 0 → IsUnit g := by
    intro g hg
    have hv₁ : w.HasValue (R.nodeResidue₁ w ⟨g, g.2.1⟩) (e₁ (ρ₁ g)) := (he₁ (ρ₁ g) _).mpr rfl
    have hr₁ : R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 := hv₁.ne_zero hg
    have hg0 : (g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
      intro h
      apply hr₁
      have : (⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1⟩ : ↥(R.nodeIntegers w)) = 0 := Subtype.ext h
      rw [this, map_zero]

    have hu₁ : IsUnit (⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.1⟩ : ↥R.R₁.integers) := by
      refine R.R₁.isUnit_of_residue_ne_zero (fun h0 => hr₁ ?_)
      have : R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.ι (R.R₁.residue ⟨g, g.2.1.1⟩) := rfl
      rw [this, h0, map_zero]

    obtain ⟨c, hc⟩ := hval g
    obtain ⟨hcA', h₂⟩ := hsp₂ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    have hredc : red ⟨c, hcA'⟩ ≠ 0 := by
      rw [← he₂val (ρ₂ g) (red ⟨c, hcA'⟩) h₂, hagree]
      exact hg
    have hr₂ : R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 := h₂.ne_zero hredc
    have hu₂ : IsUnit (⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1.2.1⟩ : ↥R.R₂.integers) := by
      refine R.R₂.isUnit_of_residue_ne_zero (fun h0 => hr₂ ?_)
      have : R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.ι (R.R₂.residue ⟨g, g.2.1.2.1⟩) := rfl
      rw [this, h0, map_zero]

    have huV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        (g : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ V.toValuationSubring := by
      intro V hV
      have hgV := g.2.1.2.2 V hV
      refine inv_mem_of_isUnit hgV ?_
      by_contra hnu
      have hmax : (⟨(g : ↥(modularFunctionFieldBar (N * q))), hgV⟩ : ↥V.toValuationSubring) ∈ maximalIdeal _ :=
        (mem_maximalIdeal _).mpr hnu
      have h0 : V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) 0 :=
        ⟨hgV, by rw [map_zero]; exact (residue_eq_zero_iff _).mpr hmax⟩
      obtain ⟨h0A, hw0⟩ := hsp₁ V hV ⟨g, g.2.1⟩ 0 h0
      apply hg
      rw [(he₁ (ρ₁ g) _).mp hw0, show (⟨0, h0A⟩ : ↥A) = 0 from rfl, map_zero]

    have hiK : (((g : ↥(modularFunctionFieldBar (N * q)))⁻¹ : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K := by
      rw [show (((g : ↥(modularFunctionFieldBar (N * q)))⁻¹ : ↥(modularFunctionFieldBar (N * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) =
          (((g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ from rfl]
      exact inv_mem g.2.2
    let gi : ↥(R.nodeIntegersOver K w) :=
      ⟨(g : ↥(modularFunctionFieldBar (N * q)))⁻¹, ⟨⟨inv_mem_of_isUnit g.2.1.1 hu₁, inv_mem_of_isUnit g.2.1.2.1 hu₂, huV⟩, hiK⟩⟩
    exact ⟨⟨g, gi, Subtype.ext (mul_inv_cancel₀ hg0), Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩

  have hval₂ : ∀ (g : ↥(R.nodeIntegersOver K w)) (a : k),
      (arithFrobC q k N • w).HasValue
        ((ρ₂ g : ↥(arithFrobC q k N • w).toValuationSubring) : ↥(modularFunctionFieldC k N)) a ↔
      e₂ (ρ₂ g) = a := by
    intro g a
    refine ⟨he₂val (ρ₂ g) a, fun h => ?_⟩
    obtain ⟨c, hc⟩ := hval g
    obtain ⟨hcA', h₂⟩ := hsp₂ V₀ hV₀ ⟨g, g.2.1⟩ c hc
    rw [← h, he₂val (ρ₂ g) (red ⟨c, hcA'⟩) h₂]
    exact h₂
  exact ⟨ρ₁, ρ₂, e₁, e₂, hagree, he₂0, hunit, hρ₁, hρ₂, he₁, hval₂⟩

end RingHalfData

end
end G

section Tuple
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem nodeResidue_nodeConst_eq_zero (R : ProlongationTuple P)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (w : Place k (modularFunctionFieldC k N))
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : NodeLocalized.redRestrict red K ϖ = 0) :
    R.nodeResidue₁ w ⟨R.nodeConst K w ϖ, (R.nodeConst K w ϖ).2.1⟩ = 0 ∧
      R.nodeResidue₂ w ⟨R.nodeConst K w ϖ, (R.nodeConst K w ϖ).2.1⟩ = 0 := by

  set a : A := Subring.inclusion inf_le_left ϖ with ha_def
  have ha : red a = 0 := hϖ0
  have hres : IsLocalRing.residue A a = 0 :=
    (IsLocalRing.residue_eq_zero_iff a).mpr ((hker_of_tuple R a).mp ha)
  constructor
  · show R.ι (R.R₁.residue ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
        (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩) = 0
    rw [R.R₁.residue_algebraMap a, hres, map_zero, map_zero]
  · show R.ι (R.R₂.residue ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ),
        (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩) = 0
    rw [R.R₂.residue_algebraMap a, hres, map_zero, map_zero]

end Tuple

private theorem exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728_exists
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (h0 : w.evalAt (jGeomGen k N) ≠ 0) (h1728 : w.evalAt (jGeomGen k N) ≠ 1728)
    (hsp₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsp₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  obtain ⟨ϖ', hϖ', eK, ε₀, heK, hε₀, hqe₀⟩ :=
    NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red (hker_of_tuple R) K
  obtain ⟨ε, hε, hqe⟩ :=
    exists_isUnit_and_natCast_eq_pow_mul_of_forall_redRestrict_eq_zero_iff ϖ ϖ' hϖ hϖ' eK ε₀ hε₀ hqe₀
  obtain ⟨c, -, -, u, hu, hnode⟩ := R.exists_nodeCoordinates_levelOneNodeCoord (hker_of_tuple R) hqN hq w hw hfix
    (w.evalAt (jGeomGen k N)) rfl h0 h1728 K ϖ hϖ eK ε hε hqe
  obtain ⟨ρ₁, ρ₂, e₁, e₂, hagree, he₂0, hunit, hρ₁, hρ₂, hval₁, hval₂⟩ := exists_ringHalfData R K w hw hsp₁ hsp₂
  have hϖ0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  obtain ⟨hc₁, hc₂⟩ := nodeResidue_nodeConst_eq_zero R K w ϖ hϖ0
  have hz₁ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → ρ₁ g = 0 := fun g hg =>
    Subtype.ext (by rw [hρ₁ g, hg]; rfl)
  have hz₂ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 → ρ₂ g = 0 := fun g hg =>
    Subtype.ext (by rw [hρ₂ g, hg]; rfl)
  have hz₁' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₁ g = 0 → R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 := fun g hg => by
    rw [← hρ₁ g, hg]; rfl
  have hz₂' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₂ g = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 := fun g hg => by
    rw [← hρ₂ g, hg]; rfl
  have hϖ₁ : ρ₁ (R.nodeConst K w ϖ) = 0 := hz₁ _ hc₁
  have hϖ₂ : ρ₂ (R.nodeConst K w ϖ) = 0 := hz₂ _ hc₂
  have hne₁ : ∀ y : ↥(R.nodeIntegersOver K w), w.ord (R.nodeResidue₁ w ⟨y, y.2.1⟩) = 1 → ρ₁ y ≠ 0 :=
    fun y hy h => by rw [hz₁' y h, w.ord_zero] at hy; exact zero_ne_one hy
  have hne₂ : ∀ x : ↥(R.nodeIntegersOver K w),
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x, x.2.1⟩) = 1 → ρ₂ x ≠ 0 :=
    fun x hx h => by rw [hz₂' x h, (arithFrobC q k N • w).ord_zero] at hx; exact zero_ne_one hx
  have hsat₁' : ∀ y : ↥(R.nodeIntegersOver K w), w.ord (R.nodeResidue₁ w ⟨y, y.2.1⟩) = 1 →
      ∀ g : ↥(R.nodeIntegersOver K w), e₁ (ρ₁ g) = 0 → ∃ b, ρ₁ g = ρ₁ y * ρ₁ b := by
    intro y hy g hg
    by_cases hg0 : ρ₁ g = 0
    · exact ⟨0, by rw [hg0, map_zero, mul_zero]⟩
    · have hpos : 0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) := by
        rw [← hρ₁ g]
        exact ord_pos_of_hasValue_zero w ((hval₁ (ρ₁ g) 0).mpr hg) (fun h0' => hg0 (Subtype.ext h0'))
      obtain ⟨b, hb⟩ := hsat₁ g y hpos hy
      exact ⟨b, Subtype.ext (by push_cast; rw [hρ₁, hρ₁, hρ₁]; exact hb)⟩
  have hsat₂' : ∀ x : ↥(R.nodeIntegersOver K w), (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x, x.2.1⟩) = 1 →
      ∀ g : ↥(R.nodeIntegersOver K w), e₂ (ρ₂ g) = 0 → ∃ b, ρ₂ g = ρ₂ x * ρ₂ b := by
    intro x hx g hg
    by_cases hg0 : ρ₂ g = 0
    · exact ⟨0, by rw [hg0, map_zero, mul_zero]⟩
    · have hpos : 0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) := by
        rw [← hρ₂ g]
        exact ord_pos_of_hasValue_zero (arithFrobC q k N • w) ((hval₂ g 0).mpr hg)
          (fun h0' => hg0 (Subtype.ext h0'))
      obtain ⟨b, hb⟩ := hsat₂ g x hpos hx
      exact ⟨b, Subtype.ext (by push_cast; rw [hρ₂, hρ₂, hρ₂]; exact hb)⟩
  have hker' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₁ g = 0 → ρ₂ g = 0 → ∃ b, g = R.nodeConst K w ϖ * b :=
    fun g h₁ h₂ =>
      exists_eq_nodeConst_mul_of_nodeResidue_eq_zero R K (hker_of_tuple R) w ϖ hϖ g (hz₁' g h₁) (hz₂' g h₂)
  have hring := crossing_ideals_of_saturation (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ (R.nodeConst K w ϖ) c.x c.y rfl hagree he₂0
    hunit hϖ₁ hϖ₂ (hz₁ _ c.x_fst) (hz₂ _ c.y_snd) (hne₁ _ c.y_fst) (hne₂ _ c.x_snd)
    (hsat₁' c.y c.y_fst) (hsat₂' c.x c.x_snd) hker'
  exact ⟨c, eK, ε, heK, hε, hqe, eK, u, heK, hu, hnode, hring.1, hring.2.1, hring.2.2.1, hring.2.2.2.1,
    hring.2.2.2.2.1, hring.2.2.2.2.2⟩

private theorem exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (h0 : w.evalAt (jGeomGen k N) ≠ 0) (h1728 : w.evalAt (jGeomGen k N) ≠ 1728)
    (hsp₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsp₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (c₀ : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
      Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} ∧
      Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} ∧
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  obtain ⟨ϖ', hϖ', eK, ε₀, heK, hε₀, hqe₀⟩ :=
    NodeLocalized.exists_forall_redRestrict_eq_zero_iff_and_natCast_eq_pow_mul red (hker_of_tuple R) K
  obtain ⟨ε, hε, hqe⟩ :=
    exists_isUnit_and_natCast_eq_pow_mul_of_forall_redRestrict_eq_zero_iff ϖ ϖ' hϖ hϖ' eK ε₀ hε₀ hqe₀
  obtain ⟨c, -, -, u, hu, hnode⟩ := R.exists_nodeCoordinates_levelOneNodeCoord (hker_of_tuple R) hqN hq w hw hfix
    (w.evalAt (jGeomGen k N)) rfl h0 h1728 K ϖ hϖ eK ε hε hqe
  obtain ⟨ρ₁, ρ₂, e₁, e₂, hagree, he₂0, hunit, hρ₁, hρ₂, hval₁, hval₂⟩ := exists_ringHalfData R K w hw hsp₁ hsp₂
  have hϖ0 : NodeLocalized.redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
  obtain ⟨hc₁, hc₂⟩ := nodeResidue_nodeConst_eq_zero R K w ϖ hϖ0
  have hz₁ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → ρ₁ g = 0 := fun g hg =>
    Subtype.ext (by rw [hρ₁ g, hg]; rfl)
  have hz₂ : ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 → ρ₂ g = 0 := fun g hg =>
    Subtype.ext (by rw [hρ₂ g, hg]; rfl)
  have hz₁' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₁ g = 0 → R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 := fun g hg => by
    rw [← hρ₁ g, hg]; rfl
  have hz₂' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₂ g = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 := fun g hg => by
    rw [← hρ₂ g, hg]; rfl
  have hϖ₁ : ρ₁ (R.nodeConst K w ϖ) = 0 := hz₁ _ hc₁
  have hϖ₂ : ρ₂ (R.nodeConst K w ϖ) = 0 := hz₂ _ hc₂
  have hne₁ : ∀ y : ↥(R.nodeIntegersOver K w), w.ord (R.nodeResidue₁ w ⟨y, y.2.1⟩) = 1 → ρ₁ y ≠ 0 :=
    fun y hy h => by rw [hz₁' y h, w.ord_zero] at hy; exact zero_ne_one hy
  have hne₂ : ∀ x : ↥(R.nodeIntegersOver K w),
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x, x.2.1⟩) = 1 → ρ₂ x ≠ 0 :=
    fun x hx h => by rw [hz₂' x h, (arithFrobC q k N • w).ord_zero] at hx; exact zero_ne_one hx
  have hsat₁' : ∀ y : ↥(R.nodeIntegersOver K w), w.ord (R.nodeResidue₁ w ⟨y, y.2.1⟩) = 1 →
      ∀ g : ↥(R.nodeIntegersOver K w), e₁ (ρ₁ g) = 0 → ∃ b, ρ₁ g = ρ₁ y * ρ₁ b := by
    intro y hy g hg
    by_cases hg0 : ρ₁ g = 0
    · exact ⟨0, by rw [hg0, map_zero, mul_zero]⟩
    · have hpos : 0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) := by
        rw [← hρ₁ g]
        exact ord_pos_of_hasValue_zero w ((hval₁ (ρ₁ g) 0).mpr hg) (fun h0' => hg0 (Subtype.ext h0'))
      obtain ⟨b, hb⟩ := hsat₁ g y hpos hy
      exact ⟨b, Subtype.ext (by push_cast; rw [hρ₁, hρ₁, hρ₁]; exact hb)⟩
  have hsat₂' : ∀ x : ↥(R.nodeIntegersOver K w), (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨x, x.2.1⟩) = 1 →
      ∀ g : ↥(R.nodeIntegersOver K w), e₂ (ρ₂ g) = 0 → ∃ b, ρ₂ g = ρ₂ x * ρ₂ b := by
    intro x hx g hg
    by_cases hg0 : ρ₂ g = 0
    · exact ⟨0, by rw [hg0, map_zero, mul_zero]⟩
    · have hpos : 0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) := by
        rw [← hρ₂ g]
        exact ord_pos_of_hasValue_zero (arithFrobC q k N • w) ((hval₂ g 0).mpr hg)
          (fun h0' => hg0 (Subtype.ext h0'))
      obtain ⟨b, hb⟩ := hsat₂ g x hpos hx
      exact ⟨b, Subtype.ext (by push_cast; rw [hρ₂, hρ₂, hρ₂]; exact hb)⟩
  have hker' : ∀ g : ↥(R.nodeIntegersOver K w), ρ₁ g = 0 → ρ₂ g = 0 → ∃ b, g = R.nodeConst K w ϖ * b :=
    fun g h₁ h₂ =>
      exists_eq_nodeConst_mul_of_nodeResidue_eq_zero R K (hker_of_tuple R) w ϖ hϖ g (hz₁' g h₁) (hz₂' g h₂)
  have hring := crossing_ideals_of_saturation (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ (R.nodeConst K w ϖ) c.x c.y rfl hagree he₂0
    hunit hϖ₁ hϖ₂ (hz₁ _ c.x_fst) (hz₂ _ c.y_snd) (hne₁ _ c.y_fst) (hne₂ _ c.x_snd)
    (hsat₁' c.y c.y_fst) (hsat₂' c.x c.x_snd) hker'
  have hx : Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} := by
    rw [span_pair_eq_ker_fst (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ _ _ rfl hagree he₂0 hϖ₁ (hz₁ _ c.x_fst) (hsat₂' c.x c.x_snd) hker',
      span_pair_eq_ker_fst (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ _ _ rfl hagree he₂0 hϖ₁ (hz₁ _ c₀.x_fst) (hsat₂' c₀.x c₀.x_snd) hker']
  have hy : Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} := by
    rw [span_pair_eq_ker_snd (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ _ _ rfl hagree he₂0 hϖ₂ (hz₂ _ c.y_snd) (hsat₁' c.y c.y_fst) hker',
      span_pair_eq_ker_snd (e₁.comp ρ₁) ρ₁ ρ₂ e₁ e₂ _ _ rfl hagree he₂0 hϖ₂ (hz₂ _ c₀.y_snd) (hsat₁' c₀.y c₀.y_fst) hker']
  exact ⟨c, hx, hy, eK, ε, heK, hε, hqe, eK, u, heK, hu, hnode, hring.1, hring.2.1, hring.2.2.1, hring.2.2.2.1,
    hring.2.2.2.2.1, hring.2.2.2.2.2⟩

end NodeCrossingAux

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (h0 : w.evalAt (jGeomGen k N) ≠ 0) (h1728 : w.evalAt (jGeomGen k N) ≠ 1728)
    (hsp₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsp₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (c₀ : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
      Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} ∧
      Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} ∧
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by
  exact NodeCrossingAux.exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728 R hqN hq K w hw hfix h0 h1728 hsp₁ hsp₂ hsat₁ hsat₂ c₀ ϖ hϖ

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_ne_zero_of_ne_1728 (solution)
