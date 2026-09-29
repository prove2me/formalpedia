-- Prove2me | solution 1 for ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bc8c131f-e3f0-5881-a2f4-af2e3d95c365

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_HahnSeries_RamificationBound
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_HahnSeries_hasRamBound_C
import Theorems.Thm_HahnSeries_hasRamBound_natCast
import Theorems.Thm_HahnSeries_hasRamBound_single_one
import Theorems.Thm_HahnSeries_HasRamBound_add
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_three_of_isRoot_at_zero_of_odd
import Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_two_of_isRoot_at_1728_of_odd
import Theorems.Thm_ModularCurve_isRoot_map_Phi_apply_jBar
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

open HahnSeries Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand jq ModularPolynomialData FunctionFieldGeneration modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_full isRoot_map_Phi_apply_jBar adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData"
p2m_open "ModularCurve"

private lemma algebraMap_hahnSeries_eq_C (a : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

private lemma forall_hasRamBound_of_embedding (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (s : HahnSeries ℚ (AlgebraicClosure ℚ)) {d : ℕ} (hd : 0 < d)
    (hs : HasRamBound d s)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        s)).IsRoot r → HasRamBound d r)
    (ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) →ₐ[AlgebraicClosure ℚ]
      HahnSeries ℚ (AlgebraicClosure ℚ))
    (hψj : ψ (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = s)
    (x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    HasRamBound d (ψ x) := by
  classical
  have halg : ∀ a : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ)
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a ∈
        (puiseuxRamSubfield (AlgebraicClosure ℚ) hd).comap
          (ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) →+*
            HahnSeries ℚ (AlgebraicClosure ℚ)) := by
    intro a
    rw [Subfield.mem_comap]
    show ψ (algebraMap _ _ a) ∈ _
    rw [AlgHom.commutes, algebraMap_hahnSeries_eq_C]
    exact (mem_puiseuxRamSubfield_iff hd).mpr (HahnSeries.hasRamBound_C a)
  have hmemS : ∀ z : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)),
      z ∈ ((puiseuxRamSubfield (AlgebraicClosure ℚ) hd).comap
          (ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) →+*
            HahnSeries ℚ (AlgebraicClosure ℚ))).toIntermediateField halg ↔
        HasRamBound d (ψ z) := by
    intro z
    constructor
    · intro h
      exact (mem_puiseuxRamSubfield_iff hd).mp (Subfield.mem_comap.mp h)
    · intro h
      exact Subfield.mem_comap.mpr ((mem_puiseuxRamSubfield_iff hd).mpr h)
  have htop : IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩,
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩} :
        Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) ≤
      ((puiseuxRamSubfield (AlgebraicClosure ℚ) hd).comap
        (ψ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) →+*
          HahnSeries ℚ (AlgebraicClosure ℚ))).toIntermediateField halg := by
    rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · rw [SetLike.mem_coe, hmemS, hψj]
      exact hs
    · rw [SetLike.mem_coe, hmemS]
      refine htrio _ ?_
      have h2 := isRoot_map_Phi_apply_jBar (AlgebraicClosure ℚ) N data
        (HahnSeries ℚ (AlgebraicClosure ℚ)) ψ
      rwa [hψj] at h2
  rw [adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N] at htop
  exact (hmemS x).mp (htop IntermediateField.mem_top)

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "qExpand jq ModularPolynomialData FunctionFieldGeneration modularFunctionFieldFull jqd_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_full isRoot_map_Phi_apply_jBar adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData"
p2m_open "ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
private theorem engine_generic (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (j₀ : AlgebraicClosure ℚ) {d : ℕ} (hd : 0 < d)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r →
      HahnSeries.HasRamBound d r)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) -
        algebraMap (AlgebraicClosure ℚ) _ j₀)) :
    v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) -
        algebraMap (AlgebraicClosure ℚ) _ j₀) ∣ (d : ℤ) := by
  classical

  have htr := transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hinj : Function.Injective (Polynomial.aeval
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      Polynomial (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] _) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    exact transcendental_iff.mp htr p hp
  set lift := RatFunc.liftAlgHom
    (Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) with hlift
  have hlift_alg : ∀ p : Polynomial (AlgebraicClosure ℚ),
      lift.toRingHom (algebraMap _ _ p) = Polynomial.aeval
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) p := by
    intro p
    have h := RatFunc.liftAlgHom_apply_div' (φ := Polynomial.aeval _)
      (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj) p 1
    simpa using h
  letI : Algebra (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
    lift.toRingHom.toAlgebra
  have halgmap : algebraMap (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) =
      lift.toRingHom := rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :=
    IsScalarTower.of_algebraMap_eq' (lift.comp_algebraMap).symm

  haveI hFD : FiniteDimensional (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) := by
    haveI hfin := finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
    obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z ∈ Submodule.span
        ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩} :
            Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))) s := by
      rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c y _ hy =>
      have hc : (c : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) ∈
          lift.fieldRange := by
        have hrange : IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩} :
              Set ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) ≤
            lift.fieldRange := by
          rw [IntermediateField.adjoin_le_iff]
          rintro y' rfl
          refine ⟨algebraMap (Polynomial (AlgebraicClosure ℚ))
            (RatFunc (AlgebraicClosure ℚ)) Polynomial.X, ?_⟩
          rw [hlift_alg, Polynomial.aeval_X]
        exact hrange c.2
      obtain ⟨c', hc'⟩ := hc
      have hcc : c • y = c' • y := by
        show (c : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) * y =
          lift.toRingHom c' * y
        rw [hc']
      rw [hcc]
      exact Submodule.smul_mem _ c' hy

  have hp : Irreducible (Polynomial.X - Polynomial.C j₀) := Polynomial.irreducible_X_sub_C j₀
  have hroot : Polynomial.aeval j₀ (Polynomial.X - Polynomial.C j₀) = 0 := by simp
  have hder : Polynomial.aeval j₀ (Polynomial.derivative
      (Polynomial.X - Polynomial.C j₀)) ≠ 0 := by simp
  have helt : algebraMap (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
        (Polynomial.X - Polynomial.C j₀)) =
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) -
      algebraMap (AlgebraicClosure ℚ) _ j₀ := by
    rw [halgmap, hlift_alg, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  have hX : algebraMap (RatFunc (AlgebraicClosure ℚ))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
        Polynomial.X) =
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) := by
    rw [halgmap, hlift_alg, Polynomial.aeval_X]
  have hA1 := AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
    (K := AlgebraicClosure ℚ) (L := AlgebraicClosure ℚ)
    (F := ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (Polynomial.X - Polynomial.C j₀) hp j₀ hroot hder hd
    (fun ψ hψ x => by
      rw [hX] at hψ
      exact forall_hasRamBound_of_embedding N data
        (HahnSeries.C j₀ + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) hd
        (HahnSeries.HasRamBound.add (HahnSeries.hasRamBound_C j₀)
          (HahnSeries.hasRamBound_single_one hd 1))
        htrio ψ hψ x)
    v (by rwa [helt])
  rwa [helt] at hA1

private theorem ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r →
      HahnSeries.HasRamBound 3 r)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (3 : ℤ) := by
  have h0 := engine_generic N data 0 (d := 3) (by norm_num)
    (fun r hr => htrio r (by rwa [map_zero, zero_add] at hr))
    v (by simpa using hv)
  simpa using h0

private theorem ord_jBar_sub_1728_dvd_two_of_pos_of_forall_isRoot_hasRamBound (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        ((1728 : HahnSeries ℚ (AlgebraicClosure ℚ)) +
          HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r →
      HahnSeries.HasRamBound 2 r)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728)) :
    v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728) ∣ (2 : ℤ) := by
  have hC : HahnSeries.C (1728 : AlgebraicClosure ℚ) =
      (1728 : HahnSeries ℚ (AlgebraicClosure ℚ)) := map_ofNat _ 1728
  have halg : algebraMap (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) 1728 =
      (1728 : ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :=
    map_ofNat _ 1728
  have h0 := engine_generic N data 1728 (d := 2) (by norm_num)
    (fun r hr => htrio r (by rwa [hC] at hr))
    v (by rwa [halg])
  rwa [halg] at h0

theorem ord_jBar_dvd_three_of_pos_of_odd_of_data (N : ℕ) [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (3 : ℤ) :=
  ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound N data
    (fun r hr => data.hasRamBound_three_of_isRoot_at_zero_of_odd hN r hr) v hv

theorem ord_jBar_sub_1728_dvd_two_of_pos_of_odd_of_data (N : ℕ) [NeZero N] (hN : Odd N)
    (data : ModularPolynomialData N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728)) :
    v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728) ∣ (2 : ℤ) :=
  ord_jBar_sub_1728_dvd_two_of_pos_of_forall_isRoot_hasRamBound N data
    (fun r hr => data.hasRamBound_two_of_isRoot_at_1728_of_odd hN r hr) v hv

private theorem ord_jBar_dvd_three_of_pos_of_odd (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (3 : ℤ) :=
  (nonempty_modularPolynomialData N).elim fun data =>
    ord_jBar_dvd_three_of_pos_of_odd_of_data N hN data v hv

private theorem ord_jBar_sub_1728_dvd_two_of_pos_of_odd (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728)) :
    v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) - 1728) ∣ (2 : ℤ) :=
  (nonempty_modularPolynomialData N).elim fun data =>
    ord_jBar_sub_1728_dvd_two_of_pos_of_odd_of_data N hN data v hv

end ModularCurve

open HahnSeries Polynomial _root_.ModularCurve _root_.P2MW.S_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound.ModularCurve in

theorem solution (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r →
      HahnSeries.HasRamBound 3 r)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (3 : ℤ) :=
  ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound N data htrio v hv

#print axioms solution

end
end S_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound
end P2MW
export P2MW.S_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound (solution)
