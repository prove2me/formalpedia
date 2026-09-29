-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8c097f03-dbb2-521b-ad7e-bf953540b9ee

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

universe u v

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace NodeRingDictionary

theorem mapDomain_apply_eq_sum_filter {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (g : α → β) (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain g D b = ∑ a ∈ D.support.filter (fun a => g a = b), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem algebraMap_adicCompletion_injective (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] :
    Function.Injective (algebraMap B (AdicCompletion (maximalIdeal B) B)) := by
  haveI : IsHausdorff (maximalIdeal B) B := by
    rw [isHausdorff_iff]
    intro x hx
    have hmem : ∀ n : ℕ, x ∈ (maximalIdeal B) ^ n := fun n => by
      have h := hx n
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h
      exact h
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
    have hx' : x ∈ (⨅ n : ℕ, (maximalIdeal B) ^ n) := Ideal.mem_iInf.mpr hmem
    rwa [hbot, Ideal.mem_bot] at hx'
  intro x y hxy
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply] at hxy
  exact AdicCompletion.of_injective _ _ hxy

theorem isAdicComplete_span_of_irreducible {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W] (π : W) (hπ : Irreducible π) : IsAdicComplete (Ideal.span {π}) W := by
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
  infer_instance

end NodeRingDictionary

set_option maxHeartbeats 12800000 in
open ModularCurve.UVCrossingModel ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
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
    (f : ↥(R.nodeIntegersOver K w))
    [IsAlgClosed k] (hqN : ¬ q ∣ N) (hO : R.OrderLawFixed)
    (h₁ : R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0)
    (h₂ : R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ ≠ 0)
    (hιord₁ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨g, g.2.1⟩ ≠ 0 →
        w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hιord₂ : ∀ (g : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨g, g.2.1⟩ ≠ 0 →
        (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) = (n : ℤ) →
        ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ g) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (ha : 0 ≤ w.ord (R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩))
    (hb : 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩))
    (Ttot : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hTtot : ∀ V, V ∈ Ttot ↔ (V.ord ((f : ↥(modularFunctionFieldBar (N * q)))) ≠ 0 ∧ P.reduceFst V = w)) :
    ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℕ∞) =
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E))) (_ : Q.asIdeal ≠ ⊥ ∧ const (π ^ E) π ∉ Q.asIdeal),
        (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (UVCrossingModel W (π ^ E) ⧸ Ideal.span {ι (algebraMap _ _ f)})) := by
  classical

  set n₁ : ℕ := (w.ord (R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩)).toNat with hn₁
  set n₂ : ℕ := ((arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩)).toNat
    with hn₂
  have hn₁' : w.ord (R.nodeResidue₁ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) = (n₁ : ℤ) :=
    (Int.toNat_of_nonneg ha).symm
  have hn₂' : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩) = (n₂ : ℤ) :=
    (Int.toNat_of_nonneg hb).symm
  clear_value n₁ n₂

  have hf0 : (f : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0
    apply h₁
    have hz : (⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ : ↥(R.nodeIntegers w)) = 0 := Subtype.ext h0
    rw [hz, map_zero]
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (f : ↥(modularFunctionFieldBar (N * q))) hf0
  have hres₁ : R.R₁.residue ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.1⟩ ≠ 0 := by
    intro h0
    apply h₁
    show R.residue₁ ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.1⟩ = 0
    rw [residue₁_apply, h0, map_zero]
  have hres₂ : R.R₂.residue ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.2.1⟩ ≠ 0 := by
    intro h0
    apply h₂
    show R.residue₂ ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.2.1⟩ = 0
    rw [residue₂_apply, h0, map_zero]
  have hφφ := ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
    k N hqN data hKr w hwss
  have haff : IsAffineGeomPlace k N w := (hwss : IsSupersingularPlace q N k w).2.1
  have hOw := hO (f : ↥(modularFunctionFieldBar (N * q))) f.2.1.1 f.2.1.2.1 hres₁ hres₂ D hD w hφφ haff
  rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w] at hOw
  have e₁ : w.ord (R.residue₁ ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.1⟩) = (n₁ : ℤ) := hn₁'
  have e₂ : (arithFrobC q k N • w).ord (R.residue₂ ⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1.2.1⟩) = (n₂ : ℤ) :=
    hn₂'
  rw [e₁, e₂, NodeRingDictionary.mapDomain_apply_eq_sum_filter] at hOw
  have hfilter : D.support.filter (fun V => P.reduceFst V = w) = Ttot := by
    ext V
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hTtot, hD]
  rw [hfilter] at hOw
  have hsumZ : ∑ V ∈ Ttot, V.ord (f : ↥(modularFunctionFieldBar (N * q))) = (n₁ : ℤ) + n₂ := by
    rw [← hOw]
    exact Finset.sum_congr rfl fun V _ => (hD V).symm
  have hsumN : (∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) = n₁ + n₂ := by
    have hnn : ∀ V ∈ Ttot, 0 ≤ V.ord (f : ↥(modularFunctionFieldBar (N * q))) := fun V hV =>
      R.ord_nonneg_of_mem_nodeIntegers f.2.1 ((hTtot V).mp hV).2
    have hcast : ((∑ V ∈ Ttot, (V.ord ((f : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ) : ℤ) =
        ((n₁ + n₂ : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Nat.cast_add, ← hsumZ]
      exact Finset.sum_congr rfl fun V hV => Int.toNat_of_nonneg (hnn V hV)
    exact Nat.cast_injective hcast

  have hx0 : ι (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) f) ≠ 0 := by
    intro h0
    have hA : algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) f = 0 :=
      ι.injective (by rw [h0, map_zero])
    have hf00 : f = 0 :=
      NodeRingDictionary.algebraMap_adicCompletion_injective ↥(R.nodeIntegersOver K w) (by rw [hA, map_zero])
    apply h₁
    have hz : (⟨(f : ↥(modularFunctionFieldBar (N * q))), f.2.1⟩ : ↥(R.nodeIntegers w)) = 0 :=
      Subtype.ext (by rw [hf00]; rfl)
    rw [hz, map_zero]
  haveI : IsAdicComplete (Ideal.span {π}) W := NodeRingDictionary.isAdicComplete_span_of_irreducible π hπ
  obtain ⟨ab, ⟨hb', habx⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE
    (ι (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)) f))
  have htot := ModularCurve.UVCrossingModel.finsum_rank_mul_length_eq_sInf_sub_sSup π hπ E hE 1 le_rfl _ hx0 ab hb' habx
  obtain ⟨γ₂, hγ₂, hxγ₂⟩ := hιord₂ f n₂ h₂ hn₂'
  obtain ⟨γ₁, hγ₁, hxγ₁⟩ := hιord₁ f n₁ h₁ hn₁'
  have hsnd := (ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem π hπ E hE 1 le_rfl _ hx0
    ab hb' habx γ₂ hγ₂ n₂ hxγ₂).2
  have hfst := (ModularCurve.UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem π hπ E hE 1 le_rfl _ hx0
    ab hb' habx γ₁ hγ₁ n₁ hxγ₁).2
  rw [hsnd, hfst] at htot
  have harith : (((n₂ : ℤ) - -(n₁ : ℤ)).toNat : ℕ) = n₁ + n₂ := by omega
  rw [htot, hsumN, harith]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ord_eq_finsum_rank_mul_length_total_of_nodeResidue_ne_zero (solution)
