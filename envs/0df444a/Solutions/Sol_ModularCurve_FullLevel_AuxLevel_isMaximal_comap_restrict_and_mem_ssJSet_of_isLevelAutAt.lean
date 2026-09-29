-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/447d7e3a-6c51-5e59-9ff1-06bdfc70773a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd
import Theorems.Thm_ModularCurve_jqNModC_mem_chartAlgFin_of_mem
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace TD1ConnAux

theorem hι_cast {L : Type} [Field L] (q ℓ' : ℕ) (ξ : L)
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ'))) :
    ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / ((q * ℓ' : ℕ) : ℂ)) := by
  obtain ⟨ι, hι⟩ := hιξ
  exact ⟨ι, by rw [hι]; push_cast; rfl⟩

theorem levelAut_mem_chartAlgFin
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ' : ℕ) [Fact ℓ'.Prime]
    (L : Type) [Field L] [CharZero L] (ξ : L)
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField L (LaurentSeries L))
    (A₀ : Type) [CommRing A₀] [Algebra A₀ L] [Algebra A₀ ↥K] [IsScalarTower A₀ L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (γ : SL(2, ℤ)) (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ) :
    ∀ a : ↥K, a ∈ chartAlgFin A₀ (↥K) j → τ a ∈ chartAlgFin A₀ (↥K) j := by
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  intro a ha
  exact ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt (q * ℓ') M' L (q * ℓ') ξ (hι_cast q ℓ' ξ hιξ) K A₀ j hj
    (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ τ hτ a ha

theorem isLevelAutAt_symm
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M' : ¬ ℓ' ∣ M')
    (L : Type) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (γ : SL(2, ℤ)) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ) :
    ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ K τ.symm := by
  obtain ⟨huniq, hmul, hone⟩ :=
    ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L ξ hξ hιξ K hK
  have hγ0' : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ0
  obtain ⟨τ', hτ'⟩ := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
    q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L ξ hξ hιξ K hK γ⁻¹ hγ0'
  rw [inv_inv] at hτ'

  have hprod := hmul γ⁻¹ γ hγ0' hγ0 τ τ' hτ hτ'
  rw [mul_inv_cancel] at hprod
  have h1 : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') 1 K 1 := hone 1 (one_mem _) (one_mem _)
  have heq : τ * τ' = 1 := huniq 1 (one_mem _) _ _ hprod h1
  have hτ'eq : τ' = τ.symm := by
    have : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_right heq
    rw [this]; rfl
  rw [← hτ'eq]; exact hτ'

theorem levelAut_symm_mem_chartAlgFin
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M' : ¬ ℓ' ∣ M')
    (L : Type) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (A₀ : Type) [CommRing A₀] [Algebra A₀ L] [Algebra A₀ ↥K] [IsScalarTower A₀ L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (γ : SL(2, ℤ)) (hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ) :
    ∀ a : ↥K, a ∈ chartAlgFin A₀ (↥K) j → τ.symm a ∈ chartAlgFin A₀ (↥K) j := by
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ'.Prime).ne_zero⟩
  have hsymm := isLevelAutAt_symm q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L ξ hξ hιξ K hK γ hγ0 τ hτ
  have hsymm' : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ') M') (γ⁻¹)⁻¹ K τ.symm := by rw [inv_inv]; exact hsymm
  intro a ha
  exact ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt (q * ℓ') M' L (q * ℓ') ξ (hι_cast q ℓ' ξ hιξ) K A₀ j hj
    (ModularCurve.FullLevel.levelH (q * ℓ') M') (γ⁻¹)⁻¹ τ.symm hsymm' a ha

end TD1ConnAux

namespace SSPermuteAux

theorem map_evalPhi {R S : Type*} [CommRing R] [CommRing S] (Φ : Polynomial (Polynomial ℤ)) (ψ : R →+* S)
    (x y : R) :
    ψ (Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y) =
      Φ.eval₂ (Polynomial.aeval (R := ℤ) (ψ x)).toRingHom (ψ y) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply Polynomial.ringHom_ext
  · intro n; simp [algebraMap_int_eq]
  · simp [Polynomial.aeval_X]

theorem kronecker_eval (q : ℕ) [Fact q.Prime] (data : ModularCurve.ModularPolynomialData q)
    (Ω : Type) [CommRing Ω] [CharP Ω q] (x y : Ω)
    (h : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    (y - x ^ q) * (y ^ q - x) = 0 := by
  have hev : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y =
      (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom Ω))).eval₂ (Polynomial.evalRingHom x) y := by
    rw [Polynomial.eval₂_map]
    congr 1
    apply Polynomial.ringHom_ext
    · intro n; simp [algebraMap_int_eq]
    · simp [Polynomial.aeval_X]
  rw [hev, ModularCurve.ModularPolynomialData.map_map_intCast_eq_of_charP q data Ω, ← Polynomial.eval_map] at h
  simpa [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow] using h

theorem isRoot_of_evalPhi_eq_zero {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (Φ : Polynomial (Polynomial ℤ)) (x y : Ω)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)).IsRoot y := by
  have e : (Polynomial.aeval (R := ℤ) x).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom Ω) x := by
    apply Polynomial.ringHom_ext
    · intro n
      show (Polynomial.aeval (R := ℤ) x) (Polynomial.C n) = _
      rw [Polynomial.aeval_C]; simp [Polynomial.eval₂RingHom]
    · simp [Polynomial.eval₂RingHom]
  show Polynomial.eval y (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)) = 0
  rw [← e, ← Polynomial.eval₂_eq_eval_map]
  exact h

theorem evalPhi_eq_zero_of_isRoot {Ω : Type*} [CommRing Ω] [Algebra ℤ Ω] (Φ : Polynomial (Polynomial ℤ)) (x y : Ω)
    (h : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)).IsRoot y) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 := by
  have e : (Polynomial.aeval (R := ℤ) x).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom Ω) x := by
    apply Polynomial.ringHom_ext
    · intro n
      show (Polynomial.aeval (R := ℤ) x) (Polynomial.C n) = _
      rw [Polynomial.aeval_C]; simp [Polynomial.eval₂RingHom]
    · simp [Polynomial.eval₂RingHom]
  rw [Polynomial.eval₂_eq_eval_map, e]
  exact h

theorem isRoot_map_of_isRoot {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (x y : R)
    (h : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).IsRoot y) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g x))).IsRoot (g y) := by
  have e : g.comp (Polynomial.eval₂RingHom (Int.castRingHom R) x) = Polynomial.eval₂RingHom (Int.castRingHom S) (g x) := by
    apply Polynomial.ringHom_ext
    · intro n; simp [Polynomial.eval₂RingHom]
    · simp [Polynomial.eval₂RingHom]
  have := h.map (f := g)
  rwa [Polynomial.map_map, e] at this

theorem map_eval_mapPhi {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    g ((Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).eval y) =
      (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g x))).eval (g y) := by
  have e : g.comp (Polynomial.eval₂RingHom (Int.castRingHom R) x) = Polynomial.eval₂RingHom (Int.castRingHom S) (g x) := by
    apply Polynomial.ringHom_ext
    · intro n; simp [Polynomial.eval₂RingHom]
    · simp [Polynomial.eval₂RingHom]
  rw [← Polynomial.eval₂_eq_eval_map, Polynomial.hom_eval₂, e, Polynomial.eval₂_eq_eval_map]

theorem isRoot_of_isRoot_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Injective g)
    (Φ : Polynomial (Polynomial ℤ)) (x y : R)
    (h : (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (g x))).IsRoot (g y)) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) x)).IsRoot y := by
  apply hg
  rw [map_zero, map_eval_mapPhi]
  exact h

theorem mem_ssJSet_iff_of_isRoot_q (q : ℕ) [Fact q.Prime] (data : ModularCurve.ModularPolynomialData q)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (x y : Ω)
    (h : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)).IsRoot y) :
    x ∈ ModularCurve.ssJSet q Ω ↔ y ∈ ModularCurve.ssJSet q Ω := by
  haveI : PerfectField Ω := IsAlgClosed.perfectField Ω
  have hk := kronecker_eval q data Ω x y (evalPhi_eq_zero_of_isRoot _ _ _ h)
  rcases mul_eq_zero.mp hk with h1 | h1
  · rw [sub_eq_zero] at h1; rw [h1]; exact (ModularCurve.pow_mem_ssJSet_iff q x).symm
  · rw [sub_eq_zero] at h1; rw [← h1]; exact ModularCurve.pow_mem_ssJSet_iff q y

end SSPermuteAux

set_option maxHeartbeats 8000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (hpres : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
    (y' : Ideal ↥(chartAlgFin A (↥K) j)) (hy' : y'.IsMaximal) (hϖy' : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y')
    (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y' → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    (Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y').IsMaximal ∧
    algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y' ∧
    (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) y' →
        φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) := by
  classical

  have hτs : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') (γ⁻¹)⁻¹ K τ.symm := by
    rw [inv_inv]; exact TD1ConnAux.isLevelAutAt_symm q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK γ hγ τ hτ
  have hpres' : ∀ a : ↥K, a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → τ.symm a ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := hpres γ⁻¹ (inv_mem hγ) τ.symm hτs
  have hsurj : Function.Surjective ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) := by
    intro b
    refine ⟨⟨τ.symm (b : ↥K), hpres' _ b.2⟩, Subtype.ext ?_⟩
    show τ (τ.symm (b : ↥K)) = b
    exact τ.apply_symm_apply _
  have hinj : Function.Injective ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpres γ hγ τ hτ)) := by
    intro a b h
    apply Subtype.ext
    exact τ.injective (by simpa using congrArg Subtype.val h)
  haveI := hy'
  refine ⟨Ideal.comap_isMaximal_of_surjective _ hsurj, ?_, ?_⟩
  ·
    rw [Ideal.mem_comap]
    convert hϖy' using 2
    apply Subtype.ext
    show τ ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = _
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  ·
    intro Ω _ _ _ _ φ hker
    obtain ⟨τE, hτE⟩ : ∃ τE : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
        (τE : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) = (τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (hpres γ hγ τ hτ) :=
      ⟨RingEquiv.ofBijective _ ⟨hinj, hsurj⟩, rfl⟩

    have hkerψ : RingHom.ker (φ.comp τE.symm.toRingHom) = y' := by
      ext c
      rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, hker, Ideal.mem_comap, ← hτE]
      show (τE (τE.symm c)) ∈ y' ↔ c ∈ y'
      rw [RingEquiv.apply_symm_apply]
    have hssψ := hss' Ω (φ.comp τE.symm.toRingHom) hkerψ
    have hφ : ∀ c, φ c = (φ.comp τE.symm.toRingHom) (τE c) := fun c => by simp

    have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
    have hqK : ModularCurve.jqNModC L q ∈ K := by
      rw [hK]; exact ModularCurve.FullLevel.jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd q ℓ M' L q
        ⟨q * ℓ ^ 2 * M', by ring⟩
    have hqC : (⟨_, hqK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j := ModularCurve.jqNModC_mem_chartAlgFin_of_mem L K A j hj q hq1 hqK
    have hwK : ModularCurve.jqNModC L (q * ℓ) ∈ K := by
      rw [hK]; exact ModularCurve.FullLevel.jqNModC_mem_laurentBaseChange_xHFunctionField_levelH_of_dvd q ℓ M' L (q * ℓ)
        ⟨q * ℓ * M', by ring⟩
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    have hwC : (⟨_, hwK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j :=
      ModularCurve.jqNModC_mem_chartAlgFin_of_mem L K A j hj (q * ℓ) (lt_of_lt_of_le hq1 (Nat.le_mul_of_pos_right _ (Fact.out : ℓ.Prime).pos)) hwK
    obtain ⟨jq', hjq'⟩ : ∃ jq' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), jq' = ⟨⟨_, hqK⟩, hqC⟩ := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), w = ⟨⟨_, hwK⟩, hwC⟩ := ⟨_, rfl⟩
    obtain ⟨dq, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm q
    obtain ⟨dℓ, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm ℓ

    obtain ⟨coeC, hcoeC⟩ : ∃ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries L, ∀ c, f c = ((c : ↥K) : LaurentSeries L) :=
      ⟨K.val.toRingHom.comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom, fun _ => rfl⟩
    have hcoeC_inj : Function.Injective coeC := fun a b h => Subtype.ext (Subtype.ext (by simpa [hcoeC] using h))

    have hj1 : ((AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = j := rfl
    have ej : ModularCurve.coeffEmb L ModularCurve.jq = ModularCurve.jqModC L := by
      rw [← ModularCurve.jqModC_rat]; exact ModularCurve.map_jqModC (algebraMap ℚ L)
    have rel1 : (dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
        (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j))).IsRoot jq' := by
      apply SSPermuteAux.isRoot_of_isRoot_map coeC hcoeC_inj
      rw [hcoeC, hcoeC, hj1, hj, hjq', ej]
      have e1 : ModularCurve.jqModC L = ModularCurve.jqNModC L 1 := (ModularCurve.qExpand_one_apply (ModularCurve.jqModC L)).symm
      rw [e1]
      apply SSPermuteAux.isRoot_of_evalPhi_eq_zero
      have e2 : ModularCurve.jqNModC L (1 * q) = ModularCurve.jqNModC L q := ModularCurve.qExpand_congr (one_mul q) _
      have h19 := ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero dq L 1
      rw [e2] at h19
      exact h19
    have rel2 : (dℓ.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) jq')).IsRoot w := by
      apply SSPermuteAux.isRoot_of_isRoot_map coeC hcoeC_inj
      rw [hcoeC, hcoeC, hjq', hw]
      apply SSPermuteAux.isRoot_of_evalPhi_eq_zero
      exact ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero dℓ L q

    have hfix : τ (w : ↥K) = (w : ↥K) := by
      have hmemj : ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
        have ej : ModularCurve.coeffEmb L ModularCurve.jq = ModularCurve.jqModC L := by
          rw [← ModularCurve.jqModC_rat]; exact ModularCurve.map_jqModC (algebraMap ℚ L)
        rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull, ← ej]
        exact ModularCurve.coeffEmb_mem_laurentBaseChange L (ModularCurve.modularFunctionField_le_full M' (ModularCurve.jq_mem M'))
      have key := (ModularCurve.FullLevel.AuxLevel.forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand_gamma0_of_exists_ringHom
        q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK).2 (w : ↥K)
      exact key.mpr ⟨ModularCurve.jqModC L, hmemj, by rw [hw]; rfl⟩ γ hγ τ hτ
    have hτEw : τE w = w := by
      apply Subtype.ext; rw [← hfix]; exact congrArg (fun f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) => ((f w : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K)) hτE

    have s1 : (φ.comp τE.symm.toRingHom) jq' ∈ ModularCurve.ssJSet q Ω :=
      (SSPermuteAux.mem_ssJSet_iff_of_isRoot_q q dq Ω _ _ (SSPermuteAux.isRoot_map_of_isRoot _ _ _ _ rel1)).mp hssψ
    have s2 : (φ.comp τE.symm.toRingHom) w ∈ ModularCurve.ssJSet q Ω :=
      (ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData q ℓ hℓq dℓ Ω _ _
        (SSPermuteAux.isRoot_map_of_isRoot _ _ _ _ rel2)).mp s1
    have s3 : φ w ∈ ModularCurve.ssJSet q Ω := by rw [hφ, hτEw]; exact s2
    have s4 : φ jq' ∈ ModularCurve.ssJSet q Ω :=
      (ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData q ℓ hℓq dℓ Ω _ _
        (SSPermuteAux.isRoot_map_of_isRoot φ _ _ _ rel2)).mpr s3
    exact (SSPermuteAux.mem_ssJSet_iff_of_isRoot_q q dq Ω _ _ (SSPermuteAux.isRoot_map_of_isRoot φ _ _ _ rel1)).mpr s4

end S_ModularCurve_FullLevel_AuxLevel_isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_isMaximal_comap_restrict_and_mem_ssJSet_of_isLevelAutAt (solution)
