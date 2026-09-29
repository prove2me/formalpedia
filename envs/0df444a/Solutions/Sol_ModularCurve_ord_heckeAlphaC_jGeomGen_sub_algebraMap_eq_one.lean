-- Prove2me | solution 1 for ModularCurve.ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/956f19e2-c381-518b-809c-47f886f68a80

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace PlaceCast
p2m_open "AlgebraicCurve"

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def cast {E E' : IntermediateField K L} (h : E = E') (y : Place K ↥E) : Place K ↥E' := h ▸ y

theorem cast_rfl {E : IntermediateField K L} (y : Place K ↥E) : cast rfl y = y := rfl

theorem ord_cast {E E' : IntermediateField K L} (h : E = E') (y : Place K ↥E)
    (x : L) (hx : x ∈ E) (hx' : x ∈ E') :
    (cast h y).ord ⟨x, hx'⟩ = y.ord ⟨x, hx⟩ := by
  subst h; rfl

theorem ord_sub_algebraMap_cast {E E' : IntermediateField K L} (h : E = E') (y : Place K ↥E)
    (x : L) (hx : x ∈ E) (hx' : x ∈ E') (c : K) :
    (cast h y).ord (⟨x, hx'⟩ - algebraMap K ↥E' c) = y.ord (⟨x, hx⟩ - algebraMap K ↥E c) := by
  subst h; rfl

theorem evalAt_cast {E E' : IntermediateField K L} (h : E = E') (y : Place K ↥E)
    (x : L) (hx : x ∈ E) (hx' : x ∈ E') :
    (cast h y).evalAt ⟨x, hx'⟩ = y.evalAt ⟨x, hx⟩ := by
  subst h; rfl

theorem mem_toValuationSubring_cast {E E' : IntermediateField K L} (h : E = E') (y : Place K ↥E)
    (x : L) (hx : x ∈ E) (hx' : x ∈ E') :
    (⟨x, hx'⟩ : ↥E') ∈ (cast h y).toValuationSubring ↔ (⟨x, hx⟩ : ↥E) ∈ y.toValuationSubring := by
  subst h; exact Iff.rfl

end AlgebraicCurve.PlaceCast

namespace AlphaUnram

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one.AlgebraicCurve ModularCurve"

theorem heckeAlphaC_jGeomGen_eq (k : Type*) [Field k] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    heckeAlphaC k N ℓ (jGeomGen k N)
      = ⟨jqModC k, modularFunctionFieldC_le_charLDegeneracyRoof k N ℓ (jqModC_mem k N)⟩ :=
  Subtype.ext (coe_heckeAlphaC k N ℓ (jGeomGen k N))

theorem main
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hy : heckeAlphaC k N ℓ (jGeomGen k N) ∈ y.toValuationSubring)
    (a : k) (ha : y.evalAt (heckeAlphaC k N ℓ (jGeomGen k N)) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    y.ord (heckeAlphaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a) = 1 := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hq' : q'.Prime := Fact.out
  have hNℓ : ¬ q' ∣ N * ℓ := by
    intro h
    rcases hq'.dvd_mul.mp h with h1 | h2
    · exact hq'N h1
    · exact hq'ℓ ((Nat.prime_dvd_prime_iff_eq hq' Fact.out).mp h2).symm

  have hroof : charLDegeneracyRoof k N ℓ = modularFunctionFieldFullC k (N * ℓ) :=
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' N ℓ hNℓ
  have hC : modularFunctionFieldC k (N * ℓ) = modularFunctionFieldFullC k (N * ℓ) :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (N * ℓ) hNℓ
  have h : charLDegeneracyRoof k N ℓ = modularFunctionFieldC k (N * ℓ) := hroof.trans hC.symm
  have hmemR : jqModC k ∈ charLDegeneracyRoof k N ℓ :=
    modularFunctionFieldC_le_charLDegeneracyRoof k N ℓ (jqModC_mem k N)

  have hαeq := heckeAlphaC_jGeomGen_eq k N ℓ
  have e2 : y.evalAt (⟨jqModC k, hmemR⟩ : ↥(charLDegeneracyRoof k N ℓ))
      = y.evalAt (heckeAlphaC k N ℓ (jGeomGen k N)) := congrArg y.evalAt hαeq.symm
  have hv : (PlaceCast.cast h y).evalAt (jGeomGen k (N * ℓ)) = a :=
    (PlaceCast.evalAt_cast h y (jqModC k) hmemR (jqModC_mem k (N * ℓ))).trans (e2.trans ha)
  have h1 := ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k (N * ℓ) hNℓ (PlaceCast.cast h y) a hv h0 h1728
  have e3 : y.ord (heckeAlphaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a)
      = y.ord ((⟨jqModC k, hmemR⟩ : ↥(charLDegeneracyRoof k N ℓ)) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a) :=
    congrArg (fun z => y.ord (z - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a)) hαeq
  exact e3.trans ((PlaceCast.ord_sub_algebraMap_cast h y (jqModC k) hmemR (jqModC_mem k (N * ℓ)) a).symm.trans h1)

theorem ord_jqModC_sub_algebraMap_eq_one_fullC
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (M : ℕ) [NeZero M] (hq'M : ¬ q' ∣ M)
    (v : Place k ↥(modularFunctionFieldFullC k M))
    (a : k) (ha : v.evalAt (⟨jqModC k, jqModC_mem_full k M⟩ : ↥(modularFunctionFieldFullC k M)) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    v.ord ((⟨jqModC k, jqModC_mem_full k M⟩ : ↥(modularFunctionFieldFullC k M))
      - algebraMap k ↥(modularFunctionFieldFullC k M) a) = 1 := by
  have hC : modularFunctionFieldFullC k M = modularFunctionFieldC k M :=
    (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' M hq'M).symm
  have hv : (PlaceCast.cast hC v).evalAt (jGeomGen k M) = a :=
    (PlaceCast.evalAt_cast hC v (jqModC k) (jqModC_mem_full k M) (jqModC_mem k M)).trans ha
  have h1 := ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k M hq'M (PlaceCast.cast hC v) a hv h0 h1728
  exact (PlaceCast.ord_sub_algebraMap_cast hC v (jqModC k) (jqModC_mem_full k M) (jqModC_mem k M) a).symm.trans h1

end AlphaUnram

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one.AlgebraicCurve ModularCurve in
theorem solution
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hy : heckeAlphaC k N ℓ (jGeomGen k N) ∈ y.toValuationSubring)
    (a : k) (ha : y.evalAt (heckeAlphaC k N ℓ (jGeomGen k N)) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    y.ord (heckeAlphaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a) = 1 :=
  AlphaUnram.main q' k N ℓ hℓN hq'N hq'ℓ y hy a ha h0 h1728

end S_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one
end P2MW
export P2MW.S_ModularCurve_ord_heckeAlphaC_jGeomGen_sub_algebraMap_eq_one (solution)
