-- Prove2me | solution 1 for ModularCurve.fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/553148c6-3563-519e-afc9-f8f6b378d7cb

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_isGalois_ord_jqModC_dvd_twelve_of_char_two
import Theorems.Thm_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_surjective
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicCurve ModularCurve KaehlerDifferential IsDedekindDomain WithZero

namespace SupersingularTop2

section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (w : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ w.ord f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem mem_of_ord_sub_pos (w : Place K F) {f : F} {c : K}
    (h : 0 < w.ord (f - algebraMap K F c)) : f ∈ w.toValuationSubring := by
  have hne : f - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have := add_mem (mem_of_ord_nonneg w hne h.le) (w.algebraMap_mem' c)
  rwa [sub_add_cancel] at this

theorem ord_eq_one_of_valuation_eq (w : Place K F) {v' : Valuation F ℤᵐ⁰}
    (hv' : v'.valuationSubring = w.toValuationSubring) {x : F} (hx : v' x = exp (-1 : ℤ)) :
    w.ord x = 1 := by
  have hE := w.isEquiv_adicValuation_of_valuationSubring_eq hv'
  have hx0 : v' x ≠ 0 := by rw [hx]; exact exp_ne_zero
  have hu0 : w.adicValuation x ≠ 0 := (hE.eq_zero).ne.mp hx0
  have hlt : w.adicValuation x < 1 := by
    refine hE.lt_one_iff_lt_one.mp ?_
    rw [hx, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  obtain ⟨ϖ, hϖ⟩ := w.heightOneSpectrum.valuation_exists_uniformizer F
  change w.adicValuation ϖ = exp (-1 : ℤ) at hϖ
  have hϖ0 : w.adicValuation ϖ ≠ 0 := by rw [hϖ]; exact exp_ne_zero
  have hϖlt : v' ϖ < 1 := by
    refine hE.lt_one_iff_lt_one.mpr ?_
    rw [hϖ, ← exp_zero]
    exact exp_lt_exp.mpr (by norm_num)
  have hϖ0' : v' ϖ ≠ 0 := (hE.eq_zero).ne.mpr hϖ0
  have hϖle : v' ϖ ≤ v' x := by
    rw [hx, ← log_le_iff_le_exp hϖ0']
    have hlog : log (v' ϖ) < 0 := (log_lt_iff_lt_exp hϖ0').mpr (by rw [exp_zero]; exact hϖlt)
    omega
  have hge : exp (-1 : ℤ) ≤ w.adicValuation x := by
    rw [← hϖ]
    exact (hE ϖ x).mp hϖle
  have hle' : log (w.adicValuation x) ≤ -1 := by
    have hlog : log (w.adicValuation x) < 0 :=
      (log_lt_iff_lt_exp hu0).mpr (by rw [exp_zero]; exact hlt)
    omega
  have hge' : -1 ≤ log (w.adicValuation x) := (le_log_iff_exp_le hu0).mpr hge
  simp only [Place.ord]
  omega

scoped instance instIsPrincipalIdealRingAdjoinSingleton (t : F) :
    IsPrincipalIdealRing (Algebra.adjoin K ({t} : Set F)) := by
  have hmem : ∀ p : Polynomial K, Polynomial.aeval t p ∈ Algebra.adjoin K ({t} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval t).codRestrict (Algebra.adjoin K ({t} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval t p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

def linGen (t : F) (c : K) : Algebra.adjoin K ({t} : Set F) :=
  ⟨t, Algebra.self_mem_adjoin_singleton K t⟩ - algebraMap K _ c

@[scoped simp] theorem coe_linGen (t : F) (c : K) :
    ((linGen t c : Algebra.adjoin K ({t} : Set F)) : F) = t - algebraMap K F c := by
  simp [linGen]

section Transcendental

variable (t : F) (htr : Transcendental K t)

include htr in
theorem linGen_ne_zero (c : K) : linGen t c ≠ 0 := by
  intro h
  have h' := congrArg (fun a : Algebra.adjoin K ({t} : Set F) => (a : F)) h
  simp only [coe_linGen, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  exact htr (by rw [h']; exact isAlgebraic_algebraMap c)

def polyEquiv : Polynomial K ≃ₐ[K] Algebra.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjective (Polynomial.aeval t) (transcendental_iff_injective.mp htr)).trans
    (Subalgebra.equivOfEq _ _ (by rw [Algebra.adjoin_singleton_eq_range_aeval]))

theorem polyEquiv_X_sub_C (c : K) :
    polyEquiv t htr (Polynomial.X - Polynomial.C c) = linGen t c := by
  apply Subtype.ext
  rw [coe_linGen]
  simp [polyEquiv, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]

include htr in

theorem prime_linGen (c : K) : Prime (linGen t c) := by
  rw [← polyEquiv_X_sub_C t htr c, MulEquiv.prime_iff]
  exact Polynomial.prime_X_sub_C c

def linPrime (c : K) : HeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) :=
  ⟨Ideal.span {linGen t c}, (Ideal.span_singleton_prime (linGen_ne_zero t htr c)).mpr
    (prime_linGen t htr c), by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact linGen_ne_zero t htr c⟩

open scoped IntermediateField.algebraAdjoinAdjoin

def basePlace (c : K) : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
  Place.ofHeightOneSpectrum (K := K) (linPrime t htr c)

theorem algebraMap_linGen (c : K) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F))
        (linGen t c) =
      IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c := by
  apply Subtype.ext
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap, coe_linGen]
  simp

theorem ord_basePlace (c : K) :
    (basePlace t htr c).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  rw [← algebraMap_linGen]
  refine ord_eq_one_of_valuation_eq (basePlace t htr c)
    (v' := (linPrime t htr c).valuation (IntermediateField.adjoin K ({t} : Set F))) rfl ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (linPrime t htr c).intValuation_singleton (linGen_ne_zero t htr c) rfl

theorem forall_algebraMap_mem (v : Place K (IntermediateField.adjoin K ({t} : Set F)))
    (ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring)
    (r : Algebra.adjoin K ({t} : Set F)) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F)) r ∈
      v.toValuationSubring := by
  obtain ⟨x, hx⟩ := r
  show (⟨x, IntermediateField.algebra_adjoin_le_adjoin K _ hx⟩ :
      IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = t := Set.mem_singleton_iff.mp hy
    subst hy'
    exact ht
  | algebraMap a => exact v.algebraMap_mem' a
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | mul y z hy hz ihy ihz => exact mul_mem ihy ihz

include htr in

theorem eq_basePlace_of_ord_pos (v : Place K (IntermediateField.adjoin K ({t} : Set F))) (c : K)
    (hv : 0 < v.ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)) :
    v = basePlace t htr c := by
  have ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring := mem_of_ord_sub_pos v hv
  have hw := forall_algebraMap_mem t v ht
  have hmem : linGen t c ∈ Place.center (Algebra.adjoin K ({t} : Set F)) v hw := by
    rw [Place.mem_center_iff_ord_pos v hw (linGen_ne_zero t htr c), algebraMap_linGen]
    exact hv
  have hcenter : Place.center (Algebra.adjoin K ({t} : Set F)) v hw = Ideal.span {linGen t c} := by
    haveI : (Ideal.span {linGen t c}).IsPrime := (linPrime t htr c).isPrime
    have hmax : (Ideal.span {linGen t c}).IsMaximal :=
      IsPrime.to_maximal_ideal (linPrime t htr c).ne_bot
    exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  have hc : Place.centerHeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) v hw =
      linPrime t htr c := HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hw, hc,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

include htr in

theorem ord_restrict_gen_eq_one [Algebra.IsIntegral (IntermediateField.adjoin K ({t} : Set F)) F]
    (w : Place K F) (hw : 0 < w.ord t) :
    (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
      (IntermediateField.AdjoinSimple.gen K t) = 1 := by
  have hgen : algebraMap (IntermediateField.adjoin K ({t} : Set F)) F
      (IntermediateField.AdjoinSimple.gen K t) = t := IntermediateField.AdjoinSimple.algebraMap_gen K t
  have h := Place.ord_restrict (F := IntermediateField.adjoin K ({t} : Set F)) w
    (IntermediateField.AdjoinSimple.gen K t)
  rw [hgen] at h
  have hpos : 0 < (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
      (IntermediateField.AdjoinSimple.gen K t) := by
    rw [h] at hw
    exact (pos_iff_pos_of_mul_pos hw).mp
      (by exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F)))
  have heq := eq_basePlace_of_ord_pos t htr (w.restrict (IntermediateField.adjoin K ({t} : Set F))) 0
    (by rw [map_zero, sub_zero]; exact hpos)
  have h1 := ord_basePlace t htr 0
  rw [map_zero, sub_zero, ← heq] at h1
  exact h1

end Transcendental

end Engine

section Along

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
  (ι : F →ₐ[K] M) (y : F)

def adjoinEquivAlong :
    IntermediateField.adjoin K ({y} : Set F) ≃ₐ[K] IntermediateField.adjoin K ({ι y} : Set M) :=
  (IntermediateField.equivMap (IntermediateField.adjoin K ({y} : Set F)) ι).trans
    (IntermediateField.equivOfEq (by rw [IntermediateField.adjoin_map, Set.image_singleton]))

theorem coe_adjoinEquivAlong (r : IntermediateField.adjoin K ({y} : Set F)) :
    ((adjoinEquivAlong ι y r : IntermediateField.adjoin K ({ι y} : Set M)) : M) = ι r := rfl

theorem finiteAlong_of_finiteDimensional_adjoin
    [h : FiniteDimensional (IntermediateField.adjoin K ({ι y} : Set M)) M] :
    FiniteAlong K ι := by
  letI := algebraAlong ι
  set R' := IntermediateField.adjoin K ({ι y} : Set M)
  obtain ⟨S, hS⟩ := h.fg_top
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff]
  rintro b -
  have hb : b ∈ Submodule.span R' (S : Set M) := by rw [hS]; exact Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem b hb => exact Submodule.subset_span hb
  | zero => exact zero_mem _
  | add b b' _ _ ih ih' => exact add_mem ih ih'
  | smul r' b _ ih =>
    have hc : (r' : M) = ι ((adjoinEquivAlong ι y).symm r' : IntermediateField.adjoin K ({y} : Set F)) := by
      rw [← coe_adjoinEquivAlong ι y, AlgEquiv.apply_symm_apply]
    have hr : r' • b =
        (((adjoinEquivAlong ι y).symm r' : IntermediateField.adjoin K ({y} : Set F)) : F) • b := by
      change (r' : M) * b = ι _ * b
      rw [hc]
    rw [hr]
    exact Submodule.smul_mem _ _ ih

theorem separableAlong_of_isSeparable_adjoin
    [Algebra.IsSeparable (IntermediateField.adjoin K ({ι y} : Set M)) M] :
    SeparableAlong K ι := by
  letI := algebraAlong ι
  set R := IntermediateField.adjoin K ({y} : Set F)
  set R' := IntermediateField.adjoin K ({ι y} : Set M)
  refine ⟨fun b => ?_⟩
  have hs : (minpoly R' b).Separable := Algebra.IsSeparable.isSeparable R' b
  set e := adjoinEquivAlong ι y

  set φ : R' →+* F := (algebraMap R F).comp (e.symm : R' →+* R) with hφ
  have hcomp : (algebraMap F M).comp φ = algebraMap R' M := by
    ext r'
    change ι (algebraMap R F (e.symm r')) = (r' : M)
    rw [show algebraMap R F (e.symm r') = ((e.symm r' : R) : F) from rfl, ← coe_adjoinEquivAlong ι y,
      AlgEquiv.apply_symm_apply]
  have hq : ((minpoly R' b).map φ).Separable := hs.map
  have hqb : Polynomial.aeval b ((minpoly R' b).map φ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact minpoly.aeval R' b
  exact hq.of_dvd (minpoly.dvd F b hqb)

theorem isIntegral_of_finiteAlong (hfin : FiniteAlong K ι) : ι.toRingHom.IsIntegral := by
  letI := algebraAlong ι
  haveI : Module.Finite F M := hfin
  intro m
  exact Algebra.IsIntegral.isIntegral (R := F) m

end Along

section Assembly

variable (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (N : ℕ) [NeZero N]

local notation "FF" => modularFunctionFieldFullC K N

set_option quotPrecheck false in
set_option hygiene false in

local notation "JJ" => (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)

omit [IsAlgClosed K] [CharP K 2] [NeZero N] in
theorem transcendental_JJ : Transcendental K JJ := by
  have h : Transcendental K (algebraMap FF (LaurentSeries K) JJ) :=
    ModularCurve.transcendental_jqModC K
  exact (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)).mp h

omit [IsAlgClosed K] [CharP K 2] in
theorem finrank_adjoin_JJ (hN : (N : K) ≠ 0) :
    Module.finrank (IntermediateField.adjoin K ({JJ} : Set FF)) FF = dedekindPsi N :=
  ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

omit [IsAlgClosed K] [CharP K 2] in
theorem finiteDimensional_adjoin_JJ (hN : (N : K) ≠ 0) :
    FiniteDimensional (IntermediateField.adjoin K ({JJ} : Set FF)) FF := by
  haveI : Module.Free (IntermediateField.adjoin K ({JJ} : Set FF)) FF := Module.Free.of_divisionRing _ _
  exact Module.finite_of_finrank_pos
    (by rw [finrank_adjoin_JJ K N hN]; exact ModularCurve.dedekindPsi_pos N (NeZero.ne N))

theorem main (hN : (N : K) ≠ 0) (P : Place K FF) (hP : P.ord JJ = 12) :
    14 ≤ P.ordDiff (D K FF JJ) := by
  classical

  obtain ⟨M, _instF, _instA, ι, hfin, hgal, hdvd⟩ :=
    ModularCurve.exists_isGalois_ord_jqModC_dvd_twelve_of_char_two K N hN
  haveI := hfin
  haveI := hgal
  set jM : M := ι JJ with hjM
  set EE : IntermediateField K M := IntermediateField.adjoin K ({jM} : Set M) with hEE

  have hfinA : FiniteAlong K ι := finiteAlong_of_finiteDimensional_adjoin ι JJ
  have hsepA : SeparableAlong K ι := separableAlong_of_isSeparable_adjoin ι JJ
  have hι : ι.toRingHom.IsIntegral := isIntegral_of_finiteAlong ι hfinA

  obtain ⟨P', hP'⟩ := Place.restrictAlong_surjective ι hι hfinA hsepA P
  simp only at hP'
  have hordP' : P'.ord jM = (Place.ramificationIndexAlong ι P' : ℤ) * 12 := by
    rw [hjM, Place.ord_restrictAlong ι hι P' JJ, hP', hP]
  have hepos : 0 < Place.ramificationIndexAlong ι P' := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI := isIntegral_along ι hι
    exact Place.ramificationIndex_pos (F := FF) P'
  have hpos : 0 < P'.ord jM := by rw [hordP']; positivity
  have he1 : Place.ramificationIndexAlong ι P' = 1 := by
    have h12 := hdvd P' hpos
    rw [hordP'] at h12
    obtain ⟨k, hk⟩ := h12
    have hk1 : (Place.ramificationIndexAlong ι P' : ℤ) * k = 1 := by
      have : (12 : ℤ) * ((Place.ramificationIndexAlong ι P' : ℤ) * k) = 12 * 1 := by
        rw [mul_one]; linarith [hk]
      exact mul_left_cancel₀ (by norm_num) this
    have := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hepos.le) hk1
    exact_mod_cast this
  have hord12 : P'.ord jM = 12 := by rw [hordP', he1]; norm_num

  have htrM : Transcendental K jM := fun halg =>
    transcendental_JJ K N ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).mp halg)
  have hx : (P'.restrict EE).ord (IntermediateField.AdjoinSimple.gen K jM) = 1 :=
    ord_restrict_gen_eq_one jM htrM P' hpos

  have hgen : algebraMap EE M (IntermediateField.AdjoinSimple.gen K jM) = jM :=
    IntermediateField.AdjoinSimple.algebraMap_gen K jM
  haveI : FiniteDimensional (IntermediateField.adjoin K
      ({algebraMap EE M (IntermediateField.AdjoinSimple.gen K jM)} : Set M)) M := by
    rw [hgen]; exact hfin
  have hH := AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois
    (K := K) (E := EE) (M := M) 2 (IntermediateField.AdjoinSimple.gen K jM) P' hx 2
    (by rw [hgen, hord12]; norm_num)
  rw [hgen, hord12] at hH
  norm_num at hH

  haveI := finiteDimensional_adjoin_JJ K N hN
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({JJ} : Set FF)) FF :=
    Algebra.IsAlgebraic.of_finite _ _
  have hDjM : D K M jM ≠ 0 := D_ne_zero_of_transcendental K jM htrM
  have hpull : pullbackDiff ι (D K FF JJ) = D K M jM := by rw [pullbackDiff_D]
  have hDJ : D K FF JJ ≠ 0 := by
    intro h0
    apply hDjM
    rw [← hpull, h0, map_zero]
  have hkey := Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero
    (K := K) JJ jM ι hι P' hDJ (by rw [he1, Nat.cast_one]; exact one_ne_zero)
  rw [hpull, he1, hP'] at hkey
  simp only [Nat.cast_one, one_mul, sub_self, add_zero] at hkey
  rw [← hkey]
  exact hH

end Assembly

end SupersingularTop2
p2m_reactivate "P2MW.S_ModularCurve_fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve.SupersingularTop2"

end
p2m_reactivate "P2MW.S_ModularCurve_fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve.SupersingularTop2"

open AlgebraicCurve ModularCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (P : Place K (modularFunctionFieldFullC K N))
    (hP : P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 12) :
    14 ≤ P.ordDiff (KaehlerDifferential.D K (modularFunctionFieldFullC K N)
        (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) :=
  SupersingularTop2.main K N hN P hP

end S_ModularCurve_fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve
end P2MW
export P2MW.S_ModularCurve_fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve (solution)
