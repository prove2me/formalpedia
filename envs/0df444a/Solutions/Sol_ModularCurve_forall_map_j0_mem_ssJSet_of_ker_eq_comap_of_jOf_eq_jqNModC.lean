-- Prove2me | solution 1 for ModularCurve.forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e4fee13e-047e-5465-b1a3-e0036923427a

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.pointAddEquivOfEq_refl ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (A₀ : Type) [CommRing A₀] [Algebra A₀ ↥K]
    (D : ModularCurve.LevelModuliDatum A₀) (P₀ : LevelModuliPackageAbs A₀ D)
    (x : D.Pt ↥K)
    (hxj : ((D.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ))
    (hmem : ∀ b : P₀.B₀, P₀.classify x b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hsurj : ∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      let θ : P₀.B₀ →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
        (P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem
      let 𝔭 : Ideal P₀.B₀ := Ideal.comap θ y.asIdeal
      ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (φ : P₀.B₀ →+* Ω),
        RingHom.ker φ = 𝔭 → φ P₀.j₀ ∈ ModularCurve.ssJSet q Ω := by
  intro STK CMP toC germY θ 𝔭 Ω _ _ _ _ φ hφ
  classical

  have hθsurj : Function.Surjective θ := by
    intro c
    obtain ⟨b, hb⟩ := hsurj c.1 c.2
    exact ⟨b, Subtype.ext hb⟩
  have hkerθ : RingHom.ker θ ≤ RingHom.ker φ := by
    intro b hb
    rw [hφ]
    rw [RingHom.mem_ker] at hb
    show θ b ∈ y.asIdeal
    rw [hb]
    exact Ideal.zero_mem _

  let φ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω :=
    (Ideal.Quotient.lift (RingHom.ker θ) φ (fun b hb => hkerθ hb)).comp
      (RingHom.quotientKerEquivOfSurjective hθsurj).symm.toRingHom
  have hφ' : ∀ b : P₀.B₀, φ' (θ b) = φ b := by
    intro b
    show (Ideal.Quotient.lift (RingHom.ker θ) φ (fun b hb => hkerθ hb)) ((RingHom.quotientKerEquivOfSurjective hθsurj).symm (θ b)) = φ b
    have : (RingHom.quotientKerEquivOfSurjective hθsurj).symm (θ b) = Ideal.Quotient.mk (RingHom.ker θ) b := by
      apply (RingHom.quotientKerEquivOfSurjective hθsurj).injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk]
  have hkerφ' : RingHom.ker φ' = y.asIdeal := by
    ext c
    obtain ⟨b, rfl⟩ := hθsurj c
    rw [RingHom.mem_ker, hφ', ← RingHom.mem_ker, hφ]
    rfl

  have hssj : φ' (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω := hss Ω φ' hkerφ'

  have hjq : ((j : ↥K) : LaurentSeries L) = jqModC L := by
    rw [hj, ← jqModC_rat]; exact map_jqModC (algebraMap ℚ L)
  have h5 := ModularCurve.FullLevel.qExpand_coeffEmb_jq_mem_and_mem_chartAlgFin_laurentBaseChange_xHFunctionField q M' ℓ L K hK A
  obtain ⟨hj', hj0', hjℓK, hjℓC⟩ := h5
  have ej : (⟨ModularCurve.coeffEmb L ModularCurve.jq, hj'⟩ : ↥K) = j := Subtype.ext hj.symm
  have hjℓC' : (⟨ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq), hjℓK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := by
    have h := hjℓC
    rw [ej] at h
    exact h
  let c₁ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j
  let cℓ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ⟨⟨ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq), hjℓK⟩, hjℓC'⟩
  let cN : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := θ P₀.j₀

  let ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries L := (algebraMap ↥K (LaurentSeries L)).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    exact hab
  have hι₁ : ι c₁ = jqNModC L 1 := by
    rw [jqNModC_one, ← hjq]; rfl
  have hιℓ : ι cℓ = jqNModC L ℓ := by
    show ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq) = jqNModC L ℓ
    have : ModularCurve.coeffEmb L ModularCurve.jq = jqModC L := by rw [← hj]; exact hjq
    rw [this]; rfl
  have hclj : (P₀.classify x) P₀.j₀ = D.jOf x := by
    rw [ModularCurve.LevelModuliPackageAbs.j₀, ← D.jOf_map (P₀.classify x) P₀.univ, P₀.map_classify]
  have hgen : ∀ m n : ℕ, m = n → ∀ [NeZero m] [NeZero n], jqNModC L m = jqNModC L n := by
    intro m n h; subst h; intro _ _; rfl
  have hcomm : jqNModC L (ℓ * q) = jqNModC L (q * ℓ) := hgen _ _ (Nat.mul_comm ℓ q)
  have hιN : ι cN = jqNModC L (ℓ * q) := by
    rw [hcomm]
    show (((P₀.classify x) P₀.j₀ : ↥K) : LaurentSeries L) = jqNModC L (q * ℓ)
    rw [hclj]; exact hxj

  obtain ⟨dℓ⟩ := ModularCurve.nonempty_modularPolynomialData ℓ
  obtain ⟨dq⟩ := ModularCurve.nonempty_modularPolynomialData q
  have rel1 : dℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) c₁).toRingHom cℓ = 0 := by
    apply hι
    rw [map_zero, Polynomial.hom_eval₂, hιℓ]
    have e : ι.comp (Polynomial.aeval (R := ℤ) c₁).toRingHom = (Polynomial.aeval (R := ℤ) (jqNModC L 1)).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp [hι₁]
    rw [e]
    simpa using dℓ.eval_jqNModC_mul_eq_zero L 1
  have rel2 : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) cℓ).toRingHom cN = 0 := by
    apply hι
    rw [map_zero, Polynomial.hom_eval₂, hιN]
    have e : ι.comp (Polynomial.aeval (R := ℤ) cℓ).toRingHom = (Polynomial.aeval (R := ℤ) (jqNModC L ℓ)).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp [hιℓ]
    rw [e]
    exact dq.eval_jqNModC_mul_eq_zero L ℓ

  have toRoot : ∀ {N : ℕ} [NeZero N] (d : ModularCurve.ModularPolynomialData N) (a b : Ω),
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) a).toRingHom b = 0 →
      (d.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) a)).IsRoot b := by
    intro N _ d a b h
    have e : (Polynomial.aeval (R := ℤ) a).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom Ω) a := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp
    rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← e]
    exact h
  have push : ∀ {N : ℕ} [NeZero N] (d : ModularCurve.ModularPolynomialData N) (u v : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v = 0 →
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) (φ' u)).toRingHom (φ' v) = 0 := by
    intro N _ d u v h
    have h' := congrArg φ' h
    rw [map_zero, Polynomial.hom_eval₂] at h'
    have e : φ'.comp (Polynomial.aeval (R := ℤ) u).toRingHom = (Polynomial.aeval (R := ℤ) (φ' u)).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp
    rwa [e] at h'
  have r1 := toRoot dℓ _ _ (push dℓ c₁ cℓ rel1)
  have r2 := toRoot dq _ _ (push dq cℓ cN rel2)

  have hssℓ : φ' cℓ ∈ ModularCurve.ssJSet q Ω :=
    (ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData q ℓ hℓq dℓ Ω (φ' c₁) (φ' cℓ) r1).mp hssj

  have hKr := ModularCurve.modularPolynomial_kronecker q dq
  have hcast : Int.castRingHom Ω = (ZMod.castHom (dvd_refl q) Ω).comp (Int.castRingHom (ZMod q)) :=
    RingHom.ext_int _ _
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ' cℓ) =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl q) Ω) (φ' cℓ)).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod q))) := by
    apply Polynomial.ringHom_ext
    · intro n
      rw [hcast]
      simp
    · simp
  have hfac : dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ' cℓ)) =
      (Polynomial.C ((φ' cℓ) ^ q) - Polynomial.X) * (Polynomial.C (φ' cℓ) - Polynomial.X ^ q) := by
    rw [hcomp, ← Polynomial.map_map, hKr]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow]
  have hb : φ' cN ∈ ModularCurve.ssJSet q Ω := by
    haveI : PerfectField Ω := inferInstance
    have h := r2
    rw [hfac, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
    rcases mul_eq_zero.mp h with h | h
    · rw [sub_eq_zero] at h
      rw [← h]
      exact (ModularCurve.pow_mem_ssJSet_iff q (φ' cℓ)).mpr hssℓ
    · rw [sub_eq_zero] at h
      exact (ModularCurve.pow_mem_ssJSet_iff q (φ' cN)).mp (h ▸ hssℓ)

  rw [← hφ' P₀.j₀]
  exact hb

end S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC
end P2MW
export P2MW.S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC (solution)
