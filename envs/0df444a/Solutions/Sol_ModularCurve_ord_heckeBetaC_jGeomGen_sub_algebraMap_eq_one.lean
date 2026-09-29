-- Prove2me | solution 1 for ModularCurve.ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4a57426f-7999-5a23-bb60-cd7863ae307b

import Mathlib
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace BetaUnram

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open IsLocalRing

theorem evalAt_algebraMap (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h1 : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := rfl
  have h2 : residue v.toValuationSubring (algebraMap K v.toValuationSubring a)
      = algebraMap K v.ResidueField a := rfl
  rw [h1, h2, v.residueInv_algebraMap]

theorem evalAt_eq_of_ord_sub_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) {a : K}
    (h : 0 < v.ord (f - algebraMap K F a)) : v.evalAt f = a := by
  have hg0 : f - algebraMap K F a ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hgmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' a)
  have hmax := (v.mem_maximalIdeal_iff_ord_pos hg0 hgmem).mpr h
  rw [v.evalAt_of_mem hf]
  have hsplit : (⟨f, hf⟩ : v.toValuationSubring)
      = ⟨f - algebraMap K F a, hgmem⟩ + algebraMap K v.toValuationSubring a :=
    Subtype.ext (by show f = (f - algebraMap K F a) + algebraMap K F a; ring)
  have hres : residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
    rw [hsplit, map_add, (residue_eq_zero_iff _).mpr hmax, zero_add]
    rfl
  rw [hres, v.residueInv_algebraMap]

theorem ord_sub_pos_of_evalAt_eq (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) {a : K} (ha : v.evalAt f = a) (hfa : f ≠ algebraMap K F a) :
    0 < v.ord (f - algebraMap K F a) := by
  have hg0 : f - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hfa
  have hgmem : f - algebraMap K F a ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' a)
  refine (v.mem_maximalIdeal_iff_ord_pos hg0 hgmem).mp ?_
  rw [← residue_eq_zero_iff]
  have hres : residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
    rw [← ha]
    exact (v.algebraMap_evalAt hv hf).symm
  have hsplit : (⟨f - algebraMap K F a, hgmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - algebraMap K v.toValuationSubring a :=
    Subtype.ext (by show f - algebraMap K F a = f - algebraMap K F a; rfl)
  rw [hsplit, map_sub, hres]
  exact sub_eq_zero.mpr rfl

theorem mem_smul_and_evalAt_smul (σ : F ≃ₐ[K] F) (v : Place K F) (hv : v.IsRational)
    {f : F} (hf : f ∈ v.toValuationSubring) :
    σ f ∈ (σ • v).toValuationSubring ∧ (σ • v).evalAt (σ f) = v.evalAt f := by
  have hmem : σ f ∈ (σ • v).toValuationSubring := by
    rw [Place.smul_toValuationSubring]
    simpa [AlgEquiv.smul_def] using
      ValuationSubring.smul_mem_pointwise_smul σ f v.toValuationSubring hf
  refine ⟨hmem, ?_⟩
  by_cases hfa : f = algebraMap K F (v.evalAt f)
  · have hσf : σ f = algebraMap K F (v.evalAt f) := by
      conv_lhs => rw [hfa]
      exact σ.commutes _
    rw [hσf]
    exact evalAt_algebraMap _ _
  · have hpos := ord_sub_pos_of_evalAt_eq v hv hf rfl hfa
    apply evalAt_eq_of_ord_sub_pos (σ • v) hmem
    rw [show σ f - algebraMap K F (v.evalAt f) = σ (f - algebraMap K F (v.evalAt f)) by
      rw [map_sub, σ.commutes], Place.ord_smul]
    exact hpos

end Generic

theorem exists_algEquiv_of_eq {k L : Type*} [Field k] [Field L] [Algebra k L]
    {E E' : IntermediateField k L} (h : E' = E) (P Q : L → Prop)
    (H : ∃ τ : E' ≃ₐ[k] E', ∀ z : E', P (z : L) → Q ((τ z : E') : L)) :
    ∃ σ : E ≃ₐ[k] E, ∀ z : E, P (z : L) → Q ((σ z : E) : L) := by
  subst h
  exact H

theorem ord_sub_algebraMap_eq_one_of_coe_eq_qExpand
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (E : IntermediateField k (LaurentSeries k)) (hE : E = modularFunctionFieldC k (N * ℓ))
    (y : Place k E) (x : E) (hx : (x : LaurentSeries k) = qExpand k ℓ (jqModC k))
    (hy : x ∈ y.toValuationSubring) (a' : k) (ha' : y.evalAt x = a') (h0 : a' ≠ 0) (h1728 : a' ≠ 1728) :
    y.ord (x - algebraMap k E a') = 1 := by
  subst hE
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hq' : q'.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hq'ℓ' : ¬ q' ∣ ℓ := fun h => hq'ℓ ((Nat.prime_dvd_prime_iff_eq hq' hℓ).mp h).symm
  have hq'Nℓ : ¬ q' ∣ N * ℓ := fun h => (hq'.dvd_mul.mp h).elim hq'N hq'ℓ'
  have hNk : (N : k) ≠ 0 := fun h => hq'N ((CharP.cast_eq_zero_iff k q' N).mp h)
  have hℓk : (ℓ : k) ≠ 0 := fun h => hq'ℓ' ((CharP.cast_eq_zero_iff k q' ℓ).mp h)

  have hCF : modularFunctionFieldFullC k (N * ℓ) = modularFunctionFieldC k (N * ℓ) :=
    (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (N * ℓ) hq'Nℓ).symm
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥(modularFunctionFieldC k (N * ℓ)) ≃ₐ[k] ↥(modularFunctionFieldC k (N * ℓ)),
      ∀ z : ↥(modularFunctionFieldC k (N * ℓ)), (z : LaurentSeries k) = qExpand k ℓ (jqModC k) →
        ((σ z : ↥(modularFunctionFieldC k (N * ℓ))) : LaurentSeries k) = jqModC k := by
    refine exists_algEquiv_of_eq hCF (fun w => w = qExpand k ℓ (jqModC k)) (fun w => w = jqModC k) ?_
    obtain ⟨τ, hτ⟩ := exists_algEquiv_atkinLehner_fullC_of_prime_of_not_dvd k N ℓ hℓ hℓN hNk hℓk
    refine ⟨τ, fun z hz => ?_⟩
    obtain ⟨-, h2⟩ := hτ 1 inferInstance (one_dvd N)

    have aux : ∀ w w₁ : ↥(modularFunctionFieldFullC k (N * ℓ)), τ w = w₁ →
        (w : LaurentSeries k) = qExpand k ℓ (jqModC k) → (w₁ : LaurentSeries k) = jqModC k →
        ((τ z : ↥(modularFunctionFieldFullC k (N * ℓ))) : LaurentSeries k) = jqModC k := by
      rintro w w₁ hww₁ hw hw₁
      have hzw : z = w := Subtype.ext (hz.trans hw.symm)
      rw [hzw, hww₁, hw₁]
    exact aux _ _ h2 (qExpand_congr (one_mul ℓ) (jqModC k)) (qExpand_one_apply (jqModC k))

  have hyrat : y.IsRational :=
    (Place.isRational_iff_deg_eq_one y).mpr (place_deg_eq_one_of_isAlgClosed k (N * ℓ) y)

  obtain ⟨hmem, heval⟩ := mem_smul_and_evalAt_smul σ y hyrat hy
  have hσx : σ x = jGeomGen k (N * ℓ) := Subtype.ext (hσ x hx)
  rw [hσx] at hmem heval
  rw [← Place.ord_smul σ y, map_sub, AlgEquiv.commutes, hσx]
  exact ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k (N * ℓ) hq'Nℓ (σ • y) a'
    (heval.trans ha') h0 h1728

end BetaUnram

open BetaUnram in
theorem solution
    (q' : ℕ) [Fact q'.Prime] (k : Type*) [Field k] [CharP k q'] [IsAlgClosed k]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hq'N : ¬ q' ∣ N) (hq'ℓ : ℓ ≠ q')
    (y : Place k ↥(charLDegeneracyRoof k N ℓ))
    (hy : heckeBetaC k N ℓ (jGeomGen k N) ∈ y.toValuationSubring)
    (a' : k) (ha' : y.evalAt (heckeBetaC k N ℓ (jGeomGen k N)) = a') (h0 : a' ≠ 0) (h1728 : a' ≠ 1728) :
    y.ord (heckeBetaC k N ℓ (jGeomGen k N) - algebraMap k ↥(charLDegeneracyRoof k N ℓ) a') = 1 := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hq' : q'.Prime := Fact.out
  have hℓ : ℓ.Prime := Fact.out
  have hq'ℓ' : ¬ q' ∣ ℓ := fun h => hq'ℓ ((Nat.prime_dvd_prime_iff_eq hq' hℓ).mp h).symm
  have hq'Nℓ : ¬ q' ∣ N * ℓ := fun h => (hq'.dvd_mul.mp h).elim hq'N hq'ℓ'
  have hRC : charLDegeneracyRoof k N ℓ = modularFunctionFieldC k (N * ℓ) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' N ℓ hq'Nℓ).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (N * ℓ) hq'Nℓ).symm
  exact ord_sub_algebraMap_eq_one_of_coe_eq_qExpand q' k N ℓ hℓN hq'N hq'ℓ _ hRC y _
    (coe_heckeBetaC k N ℓ (jGeomGen k N)) hy a' ha' h0 h1728

end S_ModularCurve_ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one
end P2MW
export P2MW.S_ModularCurve_ord_heckeBetaC_jGeomGen_sub_algebraMap_eq_one (solution)
