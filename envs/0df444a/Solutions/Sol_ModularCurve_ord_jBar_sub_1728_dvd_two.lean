-- Prove2me | solution 1 for ModularCurve.ord_jBar_sub_1728_dvd_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e476b002-f8df-5a17-a9fe-04211252881b

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_JLinePlacesBar
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries
import Theorems.Thm_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
import Theorems.Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace OrdJBarSub1728
namespace Wire

open HahnSeries Polynomial WeierstrassCurve

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

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

theorem spec_hahnExpMul (n : ℕ) (hn : 0 < n) (Φ : Polynomial (Polynomial ℤ)) (j₀ : HahnSeries ℚ K) :
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

private theorem _root_.OrdJBarSub1728.Wire.algebraMap_eq_C (a : K) : algebraMap K (HahnSeries ℚ K) a = HahnSeries.C a := by
  have h1 : algebraMap K (PowerSeries K) a = PowerSeries.C a := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

p2m_export "OrdJBarSub1728.Wire" "algebraMap_eq_C"
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

theorem transcendental_1728_add_single_two :
    Transcendental ℚ ((1728 : 𝕂) + HahnSeries.single (2 : ℚ) (1 : ℚ̄)) := by
  refine transcendental_rat_of_qbar _ (fun halg => ?_)
  have h1728 : IsAlgebraic ℚ̄ ((1728 : ℕ) : 𝕂) := isAlgebraic_nat 1728
  rw [Nat.cast_ofNat] at h1728
  have hsq : IsAlgebraic ℚ̄ (HahnSeries.single (2 : ℚ) (1 : ℚ̄) : 𝕂) := by
    have := (IsIntegral.sub halg.isIntegral h1728.isIntegral).isAlgebraic
    simpa using this
  refine transcendental_single_one (K := ℚ̄) (IsAlgebraic.of_pow (n := 2) (by norm_num) ?_)
  rw [HahnSeries.single_pow, one_pow]
  have h2 : (2 : ℕ) • (1 : ℚ) = 2 := by norm_num
  rwa [h2]

theorem j_eq_1728_add_single_two_one (𝓔 : WeierstrassCurve (PowerSeries K)) (hΔ : IsUnit 𝓔.Δ)
    (hc6 : 𝓔.c₆ ^ 2 = 𝓔.Δ * PowerSeries.X ^ 2) :
    haveI : 𝓔.IsElliptic := ⟨hΔ⟩
    (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (1728 : HahnSeries ℚ K) + HahnSeries.single (2 : ℚ) (1 : K) := by
  haveI : 𝓔.IsElliptic := ⟨hΔ⟩
  have hWΔ : IsUnit (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ.map _
  have hΔj : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ *
      (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).j
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', ← mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  have hc4c6 : 𝓔.c₄ ^ 3 - 𝓔.c₆ ^ 2 = 1728 * 𝓔.Δ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hc4' : (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).c₄ ^ 3
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ K)).Δ
        * ((1728 : HahnSeries ℚ K) + HahnSeries.single (2 : ℚ) (1 : K)) := by
    have hc4'' : 𝓔.c₄ ^ 3 = 𝓔.Δ * (1728 + PowerSeries.X ^ 2) := by
      have := hc4c6; linear_combination this + hc6
    rw [WeierstrassCurve.map_c₄, ← map_pow, hc4'', map_mul, WeierstrassCurve.map_Δ,
      map_add, map_ofNat, map_pow, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow, one_pow]
    congr 3
    simp [nsmul_eq_mul]
  exact hWΔ.mul_left_cancel (hΔj.trans hc4')

theorem hasRamBound_two_of_isRoot_at_1728
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      ((1728 : HahnSeries ℚ (AlgebraicClosure ℚ)) + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r) :
    HahnSeries.HasRamBound 2 r := by
  classical

  obtain ⟨𝓔, hΔ, hc⟩ :=
    WeierstrassCurve.exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries
      (AlgebraicClosure ℚ) two_ne_zero three_ne_zero
  haveI h𝓔E : 𝓔.IsElliptic := ⟨hΔ⟩
  have hjW : (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j = (1728 : 𝕂) + HahnSeries.single (2 : ℚ) (1 : ℚ̄) :=
    j_eq_1728_add_single_two_one 𝓔 hΔ hc
  have ht : Transcendental ℚ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j := by
    rw [hjW]; exact transcendental_1728_add_single_two

  have hτj : hahnExpMul 2 (by norm_num) ((1728 : 𝕂) + HahnSeries.single (1 : ℚ) (1 : ℚ̄))
      = (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j := by
    rw [map_add, map_ofNat, hahnExpMul_single, one_mul, hjW]
    norm_num
  have hτroot : (spec data.Φ (𝓔.map (HahnSeries.ofPowerSeries ℚ ℚ̄)).j).IsRoot
      (hahnExpMul 2 (by norm_num) r) := by
    rw [← hτj, spec_hahnExpMul]
    show Polynomial.eval _ _ = 0
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, show Polynomial.eval r (spec data.Φ _) = 0 from hroot,
      map_zero]

  have hmemL : ∀ y : 𝕂, y ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos ↔ HasRamBound 1 y :=
    fun y => HahnSeries.mem_puiseuxRamSubfield_iff Nat.one_pos
  have hτrL : hahnExpMul 2 (by norm_num) r ∈ HahnSeries.puiseuxRamSubfield ℚ̄ Nat.one_pos := by
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
  exact (hasRamBound_one_hahnExpMul_iff 2 (by norm_num) r).mp ((hmemL _).mp hτrL)

end OrdJBarSub1728.Wire
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728 P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728.Wire"
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728"

namespace OrdJBarSub1728

open ModularCurve AlgebraicCurve IntermediateField Polynomial

variable (N : ℕ) [NeZero N]

abbrev jb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

abbrev jNb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

@[reducible] def algRF : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
  ((algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N)).comp (jLineBarRingEquiv N).toRingHom).toAlgebra

theorem isScalarTower_RF :
    letI := algRF N
    IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) := by
  letI := algRF N
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  show algebraMap _ _ a = algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N)
    (jLineBarRingEquiv N (algebraMap _ _ a))
  rw [jLineBarRingEquiv_algebraMap]
  rfl

theorem finite_RF :
    letI := algRF N
    FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) := by
  letI := algRF N
  letI algRE : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) := (jLineBarRingEquiv N).toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N))
      (jLineBarRingEquiv N).surjective
  haveI : FiniteDimensional ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  exact Module.Finite.trans ↥(jLineBar N) ↥(modularFunctionFieldBar N)

theorem algebraMap_RF_X :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) Polynomial.X) = jb N := by
  letI := algRF N
  show ((jLineBarRingEquiv N (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) X)
    : ↥(jLineBar N)) : ↥(modularFunctionFieldBar N)) = jb N
  rw [RatFunc.algebraMap_X, jLineBarRingEquiv_X]

theorem algebraMap_RF_C (c : AlgebraicClosure ℚ) :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (Polynomial.C c))
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c := by
  letI := algRF N
  haveI := isScalarTower_RF N
  rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_RF_X_sub_C (c : AlgebraicClosure ℚ) :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (X - C c))
        = jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c := by
  letI := algRF N
  rw [map_sub, map_sub, algebraMap_RF_X, algebraMap_RF_C]

theorem eval₂_Phi_jb_jNb (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) (jNb N)
      = 0 := by

  apply Subtype.ext
  have hval : ((modularFunctionFieldBar N).toSubfield.subtype).comp
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N))
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    show ((Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N) X :
        ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (evalAtJ X)
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, ← hval] at h0
  rw [ZeroMemClass.coe_zero, ← h0]
  show ((modularFunctionFieldBar N).toSubfield.subtype) _ = _
  rw [Polynomial.hom_eval₂]
  rfl

theorem hasRamBound_C (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1 (HahnSeries.C a : HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  intro g hg
  have : g ∈ ({0} : Set ℚ) := HahnSeries.support_single_subset (a := (0 : ℚ)) (r := a) hg
  rw [Set.mem_singleton_iff] at this
  exact ⟨0, by simp [this]⟩

theorem hasRamBound_C_add_single (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1
      (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) := by
  intro g hg
  rcases (HahnSeries.support_add_subset (x := HahnSeries.C a)
      (y := HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))) hg with h | h
  · exact hasRamBound_C a h
  · have : g ∈ ({1} : Set ℚ) :=
      HahnSeries.support_single_subset (a := (1 : ℚ)) (r := (1 : AlgebraicClosure ℚ)) h
    rw [Set.mem_singleton_iff] at this
    exact ⟨1, by simp [this]⟩

theorem hasRamBound_of_one' {e : ℕ} (he : 0 < e) {y : HahnSeries ℚ (AlgebraicClosure ℚ)}
    (hy : HahnSeries.HasRamBound 1 y) : HahnSeries.HasRamBound e y := by
  intro g hg
  obtain ⟨k, hk⟩ := hy hg
  refine ⟨k * e, ?_⟩
  simp only [Nat.cast_one, div_one] at hk
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [← hk]; push_cast; field_simp

theorem forall_hasRamBound_of_roots (data : ModularPolynomialData N) (c : AlgebraicClosure ℚ) {d : ℕ} (hd : 0 < d)
    (hroots : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r → HahnSeries.HasRamBound d r)
    (ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ))
    (hψ : ψ (jb N) = HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) :
    ∀ z, HahnSeries.HasRamBound d (ψ z) := by
  let S := HahnSeries.puiseuxRamSubfield (AlgebraicClosure ℚ) (e := d) hd
  have hS : ∀ y, y ∈ S ↔ HahnSeries.HasRamBound d y := fun y => HahnSeries.mem_puiseuxRamSubfield_iff hd
  let T : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    (S.comap ψ.toRingHom).toIntermediateField (fun a => by
      show ψ (algebraMap (AlgebraicClosure ℚ) _ a) ∈ S
      have hC : algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) a = HahnSeries.C a := by
        rw [HahnSeries.algebraMap_apply']; simp
      rw [ψ.commutes, hS, hC]
      exact hasRamBound_of_one' hd (hasRamBound_C a))
  have hjb : jb N ∈ T := by
    show ψ (jb N) ∈ S
    rw [hψ, hS]
    exact hasRamBound_of_one' hd (hasRamBound_C_add_single c)
  have hjNb : jNb N ∈ T := by
    show ψ (jNb N) ∈ S
    rw [hS]
    refine hroots _ ?_
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← hψ]
    have hcomp : Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) (ψ (jb N))
        = (ψ.toRingHom).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) := by
      refine Polynomial.ringHom_ext (fun z => by simp) ?_
      simp
    rw [hcomp]
    have h := (Polynomial.hom_eval₂ data.Φ
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) ψ.toRingHom (jNb N)).symm
    rw [eval₂_Phi_jb_jNb N data, map_zero] at h
    simpa using h
  have htop := ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have hle : (⊤ : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) ≤ T := by
    rw [← htop, IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact hjb
    · exact hjNb
  intro z
  exact (hS _).mp (hle IntermediateField.mem_top)

theorem ord_jb_sub_dvd (data : ModularPolynomialData N) (c : AlgebraicClosure ℚ) {d : ℕ} (hd : 0 < d)
    (hroots : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r → HahnSeries.HasRamBound d r)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hpos : 0 < v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c)) :
    v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) ∣ (d : ℤ) := by
  letI := algRF N
  haveI := isScalarTower_RF N
  haveI := finite_RF N
  have key := AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
    (K := AlgebraicClosure ℚ) (L := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
    (X - C c) (Polynomial.irreducible_X_sub_C c) c (by simp) (by simp) hd
    (fun ψ hψ => forall_hasRamBound_of_roots N data c hd hroots ψ (by rwa [algebraMap_RF_X] at hψ)) v
    (by rwa [algebraMap_RF_X_sub_C])
  rwa [algebraMap_RF_X_sub_C] at key

theorem ord_jb_sub_1728_dvd_two
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hpos : 0 < v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728)) :
    v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) ∣ 2 := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have h := ord_jb_sub_dvd N data 1728 (d := 2) two_pos (fun r hr => by
    refine OrdJBarSub1728.Wire.hasRamBound_two_of_isRoot_at_1728 data r ?_
    have : (HahnSeries.C (1728 : AlgebraicClosure ℚ) : HahnSeries ℚ (AlgebraicClosure ℚ)) = 1728 :=
      map_ofNat _ 1728
    rwa [this] at hr) v hpos
  exact_mod_cast h

end OrdJBarSub1728
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728 P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728.Wire"

end
p2m_reactivate "P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728 P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two.OrdJBarSub1728.Wire"

theorem solution (N : ℕ) [NeZero N]
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hpos : 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728)) :
    v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ∣ 2 := by
  exact OrdJBarSub1728.ord_jb_sub_1728_dvd_two N v hpos

end S_ModularCurve_ord_jBar_sub_1728_dvd_two
end P2MW
export P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two (solution)
