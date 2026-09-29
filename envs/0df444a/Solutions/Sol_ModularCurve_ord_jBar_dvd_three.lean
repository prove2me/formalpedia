-- Prove2me | solution 1 for ModularCurve.ord_jBar_dvd_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1821b8e1-12e3-5fb3-ada8-796f439c5e95

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_HahnSeries_RamificationBound
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries
import Theorems.Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
import Theorems.Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jBar_dvd_three
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open HahnSeries Polynomial WeierstrassCurve

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

noncomputable section

namespace OrdJBarDvdThree

variable {K : Type*} [Field K]

def hahnExpMul (n : ℕ) (hn : 0 < n) : HahnSeries ℚ K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulRight (n : ℚ))
    (mul_left_injective₀ (Nat.cast_ne_zero.mpr hn.ne'))
    (fun _ _ => mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hn))

@[scoped simp] theorem hahnExpMul_single (n : ℕ) (hn : 0 < n) (q : ℚ) (c : K) :
    hahnExpMul n hn (HahnSeries.single q c) = HahnSeries.single (q * n) c := by
  unfold hahnExpMul
  rw [embDomainRingHom_apply, embDomain_single]
  rfl

@[scoped simp] theorem hahnExpMul_coeff_mul (n : ℕ) (hn : 0 < n) (r : HahnSeries ℚ K) (q : ℚ) :
    (hahnExpMul n hn r).coeff (q * n) = r.coeff q :=
  HahnSeries.embDomain_coeff

theorem hasRamBound_one_hahnExpMul_iff (n : ℕ) (hn : 0 < n) (r : HahnSeries ℚ K) :
    HasRamBound 1 (hahnExpMul n hn r) ↔ HasRamBound n r := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h q hq
    have hnq : q * n ∈ (hahnExpMul n hn r).support := by
      rw [HahnSeries.mem_support, hahnExpMul_coeff_mul]; exact hq
    obtain ⟨k, hk⟩ := h hnq
    refine ⟨k, ?_⟩
    simp only [Nat.cast_one, div_one] at hk
    field_simp
    linarith
  · intro h q hq
    obtain ⟨p, rfl⟩ : ∃ p : ℚ, p * n = q := ⟨q / n, div_mul_cancel₀ q hnQ⟩
    have hp : p ∈ r.support := by
      rw [HahnSeries.mem_support, ← hahnExpMul_coeff_mul n hn]; exact hq
    obtain ⟨k, hk⟩ := h hp
    refine ⟨k, ?_⟩
    simp only [Nat.cast_one, div_one]
    field_simp at hk
    linarith [hk]

abbrev spec (Φ : Polynomial (Polynomial ℤ)) (j₀ : HahnSeries ℚ K) : Polynomial (HahnSeries ℚ K) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) j₀)

theorem hahnExpMul_comp_eval (n : ℕ) (hn : 0 < n) (j₀ : HahnSeries ℚ K) :
    (hahnExpMul n hn).comp (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) j₀)
      = Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ K)) (hahnExpMul n hn j₀) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  simp [Polynomial.eval₂RingHom]

theorem spec_hahnExpMul (n : ℕ) (hn : 0 < n) (Φ : Polynomial (Polynomial ℤ))
    (j₀ : HahnSeries ℚ K) :
    spec Φ (hahnExpMul n hn j₀) = (spec Φ j₀).map (hahnExpMul n hn) := by
  rw [spec, spec, Polynomial.map_map, hahnExpMul_comp_eval]

theorem hasRamBound_one_ofPowerSeries (p : PowerSeries K) :
    HasRamBound 1 (HahnSeries.ofPowerSeries ℚ K p) := by
  intro q hq
  have hq' : q ∈ Set.range ((↑) : ℕ → ℚ) := by
    by_contra h
    rw [HahnSeries.mem_support, HahnSeries.ofPowerSeries_apply] at hq
    exact hq (HahnSeries.embDomain_notin_range (by simpa using h))
  obtain ⟨m, rfl⟩ := hq'
  exact ⟨(m : ℤ), by push_cast; ring⟩

theorem algebraMap_eq_C (a : K) : algebraMap K (HahnSeries ℚ K) a = HahnSeries.C a := by
  have h1 : algebraMap K (PowerSeries K) a = PowerSeries.C a := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem transcendental_single_one : Transcendental K (HahnSeries.single (1 : ℚ) (1 : K)) := by
  rw [transcendental_iff_injective]
  have heq : (Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K))).toRingHom
      = (HahnSeries.ofPowerSeries ℚ K).comp (Polynomial.coeToPowerSeries.ringHom (R := K)) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · show Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K)) (Polynomial.C a) = _
      rw [Polynomial.aeval_C, algebraMap_eq_C,
        RingHom.coe_comp, Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
    · show Polynomial.aeval (R := K) (HahnSeries.single (1:ℚ) (1:K)) Polynomial.X = _
      rw [Polynomial.aeval_X, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  intro p q hpq
  have hpq' : (HahnSeries.ofPowerSeries ℚ K) (p : PowerSeries K)
      = (HahnSeries.ofPowerSeries ℚ K) (q : PowerSeries K) := by
    have hp := congrFun (congrArg DFunLike.coe heq) p
    have hq := congrFun (congrArg DFunLike.coe heq) q
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
      Function.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply] at hp hq
    rw [← hp, ← hq]; exact hpq
  exact Polynomial.coe_injective K (HahnSeries.ofPowerSeries_injective hpq')

theorem transcendental_rat_of_qbar (x : 𝕂) (h : Transcendental ℚ̄ x) : Transcendental ℚ x := by
  rintro ⟨p, hp0, hpx⟩
  refine h ⟨p.map (algebraMap ℚ ℚ̄),
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ̄).injective).mpr hp0, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    Subsingleton.elim ((algebraMap ℚ̄ 𝕂).comp (algebraMap ℚ ℚ̄)) (algebraMap ℚ 𝕂),
    ← Polynomial.aeval_def]
  exact hpx

theorem transcendental_single_three :
    Transcendental ℚ (HahnSeries.single (3 : ℚ) (1 : ℚ̄) : 𝕂) := by
  refine transcendental_rat_of_qbar _ (fun halg => ?_)
  refine transcendental_single_one (K := ℚ̄) (IsAlgebraic.of_pow (n := 3) (by norm_num) ?_)
  rw [HahnSeries.single_pow, one_pow]
  have h3 : (3 : ℕ) • (1 : ℚ) = 3 := by norm_num
  rwa [h3]

theorem j_eq_single_three_one (𝓔 : WeierstrassCurve (PowerSeries K)) (hΔ : IsUnit 𝓔.Δ)
    (hc4 : 𝓔.c₄ ^ 3 = 𝓔.Δ * PowerSeries.X ^ 3) :
    haveI : 𝓔.IsElliptic := ⟨hΔ⟩
    (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j = HahnSeries.single (3 : ℚ) (1 : K) := by
  haveI : 𝓔.IsElliptic := ⟨hΔ⟩
  have hWΔ : IsUnit (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hΔj : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ *
      (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  have hc4' : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ * HahnSeries.single (3 : ℚ) (1 : K) := by
    rw [WeierstrassCurve.map_c₄, ← map_pow, hc4, map_mul, map_pow, HahnSeries.ofPowerSeries_X,
      HahnSeries.single_pow, one_pow, WeierstrassCurve.map_Δ]
    congr 2
    simp [nsmul_eq_mul]
  exact hWΔ.mul_left_cancel (hΔj.trans hc4')

theorem hasRamBound_three_of_isRoot_at_zero
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (r : 𝕂)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom 𝕂)
      (HahnSeries.single (1 : ℚ) (1 : ℚ̄)))).IsRoot r) :
    HahnSeries.HasRamBound 3 r := by
  classical

  obtain ⟨𝓔, hΔ, hc⟩ :=
    WeierstrassCurve.exists_isUnit_discriminant_and_c4_cube_eq_mul_X_cube_powerSeries
      ℚ̄ two_ne_zero three_ne_zero
  haveI h𝓔E : 𝓔.IsElliptic := ⟨hΔ⟩
  have hjW : (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j = HahnSeries.single (3 : ℚ) (1 : ℚ̄) :=
    j_eq_single_three_one 𝓔 hΔ hc
  have ht : Transcendental ℚ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j := by
    rw [hjW]; exact transcendental_single_three

  have hτj : hahnExpMul 3 (by norm_num) (HahnSeries.single (1 : ℚ) (1 : ℚ̄))
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j := by
    rw [hahnExpMul_single, one_mul, hjW]
    norm_num
  have hτroot : (spec data.Φ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j).IsRoot
      (hahnExpMul 3 (by norm_num) r) := by
    rw [← hτj, spec_hahnExpMul]
    show Polynomial.eval _ _ = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_hom,
      show Polynomial.eval r (spec data.Φ _) = 0 from hroot, map_zero]

  have hmemL : ∀ y : 𝕂, y ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos ↔ HasRamBound 1 y :=
    fun y => HahnSeries.mem_puiseuxRamSubfield_iff Nat.one_pos
  have hτrL : hahnExpMul 3 (by norm_num) r ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos := by
    refine ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental data
      (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)) ht (HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos)
      ?_ ?_ ?_ ?_ ?_ ?_ _ hτroot
    · rw [WeierstrassCurve.map_a₁, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₂, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₃, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₄, hmemL]; exact hasRamBound_one_ofPowerSeries _
    · rw [WeierstrassCurve.map_a₆, hmemL]; exact hasRamBound_one_ofPowerSeries _
    ·
      intro x y hns hd
      have h := WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
        𝓔 hΔ (Nat.pos_of_ne_zero (NeZero.ne N)) x y hns hd
      exact ⟨(hmemL x).mpr h.1, (hmemL y).mpr h.2⟩
  exact (hasRamBound_one_hahnExpMul_iff 3 (by norm_num) r).mp ((hmemL _).mp hτrL)

end OrdJBarDvdThree
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_dvd_three.OrdJBarDvdThree"

end
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_dvd_three.OrdJBarDvdThree"

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N]
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hpos : 0 < v.ord (ModularCurve.jBar N)) :
    v.ord (ModularCurve.jBar N) ∣ 3 := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  exact ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound N data
    (fun r hr => OrdJBarDvdThree.hasRamBound_three_of_isRoot_at_zero data r hr) v hpos

end S_ModularCurve_ord_jBar_dvd_three
end P2MW
export P2MW.S_ModularCurve_ord_jBar_dvd_three (solution)
