-- Prove2me | solution 1 for ModularCurve.moduliPlace_restrictAlong_qExpand_veluQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a8c0b674-35b7-51af-9751-976634c8d877

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_moduliPlace_restrictAlong_qExpand_fullKernelQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace P2MKcDegenC8

section Cleared

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem velu_pair_x_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      + ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
      = W.veluT x₀ y₀ * (x - x₀) + W.veluU x₀ y₀ := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination 2 * hP - 2 * hR

theorem velu_pair_y_cleared {x y x₀ y₀ : R}
    (hP : W.toAffine.Equation x y) (hR : W.toAffine.Equation x₀ y₀) :
    ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3)
      + ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3)
      = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃)
          + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)
          + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀)) := by
  rw [Affine.equation_iff] at hP hR
  simp only [veluT, veluU, veluGx, veluGy]
  linear_combination (-(2 * y) - 2 * W.a₁ * x + W.a₁ * x₀ - W.a₃) * hP
    + (2 * y + 2 * W.a₁ * x - W.a₁ * x₀ + W.a₃) * hR

end Cleared

section PairField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem addX_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - y₀) / (x - x₀)) - x₀
      = ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2)
          / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX]
  field_simp
  ring1

theorem addX_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addX x x₀ ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - x₀
      = ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
          - (W.a₂ + x + x₀) * (x - x₀) ^ 2 - x₀ * (x - x₀) ^ 2) / (x - x₀) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 hd)]
  simp only [Affine.addX, Affine.negY]
  field_simp
  ring1

theorem addY_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - y₀) / (x - x₀)) - y₀
      = ((-((y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) - y₀ * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

theorem addY_neg_sub_eq_div {x y x₀ y₀ : F} (hd : x - x₀ ≠ 0) :
    W.toAffine.addY x x₀ y ((y - W.toAffine.negY x₀ y₀) / (x - x₀)) - W.toAffine.negY x₀ y₀
      = ((-((y + y₀ + W.a₁ * x₀ + W.a₃) * (((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2
              + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
            - x * (x - x₀) ^ 2) + y * (x - x₀) ^ 3)
        - W.a₁ * ((y + y₀ + W.a₁ * x₀ + W.a₃) ^ 2 + W.a₁ * (y + y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
        - W.a₃ * (x - x₀) ^ 3) + (y₀ + W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3) / (x - x₀) ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hd)]
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  ring1

variable [DecidableEq F]

theorem velu_pair {x y x₀ y₀ : F}
    (h : W.toAffine.Nonsingular x y) (h₀ : W.toAffine.Nonsingular x₀ y₀) (hx : x ≠ x₀) :
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.1
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.1)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.1
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.1)
        = W.veluT x₀ y₀ / (x - x₀) + W.veluU x₀ y₀ / (x - x₀) ^ 2) ∧
    (((Point.some x y h + Point.some x₀ y₀ h₀).coordsOrZero.2
          - (Point.some x₀ y₀ h₀ : W.toAffine.Point).coordsOrZero.2)
        + ((Point.some x y h + -Point.some x₀ y₀ h₀).coordsOrZero.2
          - (-(Point.some x₀ y₀ h₀ : W.toAffine.Point)).coordsOrZero.2)
        = -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) / (x - x₀) ^ 3
            + W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2
            + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (x - x₀) ^ 2)) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hP : W.toAffine.Equation x y := h.1
  have hR : W.toAffine.Equation x₀ y₀ := h₀.1
  rw [Point.neg_some h₀, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  simp only [Point.coordsOrZero_some, slope_of_X_ne hx]
  refine ⟨?_, ?_⟩
  · rw [addX_sub_eq_div W hd, addX_neg_sub_eq_div W hd, ← add_div, velu_pair_x_cleared W hP hR,
      div_add_div _ _ hd (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 2 hd) (mul_ne_zero hd (pow_ne_zero 2 hd))]
    ring
  · rw [addY_sub_eq_div W hd, addY_neg_sub_eq_div W hd, ← add_div, velu_pair_y_cleared W hP hR,
      neg_div, neg_inj, div_add_div _ _ (pow_ne_zero 3 hd) (pow_ne_zero 2 hd), div_add_div _ _
        (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd),
      div_eq_div_iff (pow_ne_zero 3 hd)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hd) (pow_ne_zero 2 hd)) (pow_ne_zero 2 hd))]
    ring

end PairField

theorem sum_Icc_two_mul_eq_sum_pairs {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * n), f k = ∑ k ∈ Finset.Icc 1 n, (f k + f (2 * n + 1 - k)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : Finset.Icc 1 (2 * n) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (2 * n) := by
    ext k; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]; intro k hk hk'; simp only [Finset.mem_Icc] at hk hk'; omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  refine Finset.sum_nbij' (fun k => 2 * n + 1 - k) (fun k => 2 * n + 1 - k) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; congr 1; omega

theorem nsmul_ne_zero_of_pos_of_le {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    (Q : W.toAffine.Point) {N : ℕ} (hQ : addOrderOf Q = N) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N - 1) :
    k • Q ≠ 0 := by
  intro h
  have hdvd : N ∣ k := hQ ▸ addOrderOf_dvd_of_nsmul_eq_zero h
  have hle : N ≤ k := Nat.le_of_dvd hk1 hdvd
  omega

theorem fullKernelPin_eq_veluXY_of_odd
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hP : (Point.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    (x + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
     y + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
        (((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) =
      (W.veluX (W.oddOrderSummingSet Q n) x, W.veluY (W.oddOrderSummingSet Q n) x y) := by
  classical
  have h2n : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel (2 * n) 1
  have hord : (2 * n + 1) • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
  have hrefl : ∀ k, k ≤ 2 * n + 1 → (2 * n + 1 - k) • Q = -(k • Q) := by
    intro k hk
    rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hord]

  have haff : ∀ k, 1 ≤ k → k ≤ 2 * n →
      ∃ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀), k • Q = Point.some x₀ y₀ h₀ ∧ x ≠ x₀ := by
    intro k hk1 hk2
    have hne : k • Q ≠ 0 := nsmul_ne_zero_of_pos_of_le Q hQ hk1 (by omega)
    rcases hkQ : k • Q with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hkQ hne
    · refine ⟨x₀, y₀, h₀, rfl, ?_⟩
      intro hxx
      apply hP
      rcases Affine.Y_eq_of_X_eq h.1 h₀.1 hxx with hyy | hyy
      · have hPt : (Point.some x y h : W.toAffine.Point) = k • Q := by
          rw [hkQ]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k
      · have hPt : (Point.some x y h : W.toAffine.Point) = -(k • Q) := by
          rw [hkQ, Point.neg_some]; subst hxx; subst hyy; rfl
        rw [hPt]
        exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)

  have hpair : ∀ k ∈ Finset.Icc 1 n,
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.1
            - ((2 * n + 1 - k) • Q).coordsOrZero.1)
        = W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1)
          + W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 / (x - (k • Q).coordsOrZero.1) ^ 2) ∧
      ((((Point.some x y h : W.toAffine.Point) + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)
        + (((Point.some x y h : W.toAffine.Point) + (2 * n + 1 - k) • Q).coordsOrZero.2
            - ((2 * n + 1 - k) • Q).coordsOrZero.2)
        = -(W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2 * (2 * y + W.a₁ * x + W.a₃)
              / (x - (k • Q).coordsOrZero.1) ^ 3
            + W.veluT (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
              * (W.a₁ * (x - (k • Q).coordsOrZero.1) + y - (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2
            + (W.a₁ * W.veluU (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                - W.veluGx (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2
                  * W.veluGy (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2)
              / (x - (k • Q).coordsOrZero.1) ^ 2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨x₀, y₀, h₀, hkQ, hx⟩ := haff k hk.1 (by omega)
    rw [hrefl k (by omega), hkQ]
    exact velu_pair W h h₀ hx

  have hinj : ∀ k ∈ Finset.Icc 1 n, ∀ k' ∈ Finset.Icc 1 n,
      (k • Q).coordsOrZero = (k' • Q).coordsOrZero → k = k' := by
    intro k hk k' hk' hkk
    rw [Finset.mem_Icc] at hk hk'
    obtain ⟨x₀, y₀, h₀, hkQ, -⟩ := haff k hk.1 (by omega)
    obtain ⟨x₁, y₁, h₁, hk'Q, -⟩ := haff k' hk'.1 (by omega)
    have hpt : k • Q = k' • Q := by
      rw [hkQ, hk'Q] at hkk ⊢
      simp only [Point.coordsOrZero_some, Prod.mk.injEq] at hkk
      obtain ⟨rfl, rfl⟩ := hkk
      rfl
    have hmod := (nsmul_inj_mod (x := Q)).mp hpt
    rwa [hQ, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod

  rw [h2n]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).1)]
    simp only [veluX, oddOrderSummingSet, Finset.sum_image hinj]
  · dsimp only
    rw [sum_Icc_two_mul_eq_sum_pairs, Finset.sum_congr rfl (fun k hk => (hpair k hk).2)]
    simp only [veluY, oddOrderSummingSet, Finset.sum_image hinj, Finset.sum_neg_distrib,
      sub_eq_add_neg]

theorem coordsOrZero_eq_translationSum
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) (n : ℕ) (hQ : addOrderOf Q = 2 * n + 1)
    (φ : W.toAffine.Point →+ (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Point)
    (hφ : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (W.veluX (W.oddOrderSummingSet Q n) x)
          (W.veluY (W.oddOrderSummingSet Q n) x y) h')
    (P : W.toAffine.Point) (hP : P ∉ AddSubgroup.zmultiples Q) :
    (φ P).coordsOrZero =
      (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
          ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
       P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
          ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (AddSubgroup.zero_mem _) hP
  · obtain ⟨h', hφP⟩ := hφ x y h hP
    rw [hφP, Point.coordsOrZero_some, Point.coordsOrZero_some]
    exact (fullKernelPin_eq_veluXY_of_odd W Q n hQ h hP).symm

end P2MKcDegenC8

end

open P2MKcDegenC8 in
universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (hMs : ((M * s : ℕ) : K) ≠ 0)
    (huniq : ∀ (x : ModuliPoint M K) (v v' : Place K (modularFunctionFieldFullC K M)),
      IsModuliPlaceOf K M x v → IsModuliPlaceOf K M x v' → v = v')
    (hex : ∀ x : ModuliPoint (M * s) K, ∃ v, IsModuliPlaceOf K (M * s) x v)
    (β : modularFunctionFieldFullC K M →ₐ[K] modularFunctionFieldFullC K (M * s))
    (hβ : ∀ f : modularFunctionFieldFullC K M,
      ((β f : modularFunctionFieldFullC K (M * s)) : LaurentSeries K) =
        qExpand K s (f : LaurentSeries K))
    (hb : β.toRingHom.IsIntegral)
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic]
    (C : AddSubgroup E₀.toAffine.Point) (hC : IsAddCyclic C ∧ Nat.card C = M * s)
    (n : ℕ) (hs : s = 2 * n + 1) (Q : E₀.toAffine.Point) (hQC : Q ∈ C)
    (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).Δ ≠ 0)
    (φ : E₀.toAffine.Point →+ (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : K) (h : E₀.toAffine.Nonsingular x y),
      (.some x y h : E₀.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E₀.veluX (E₀.oddOrderSummingSet Q n) x)
          (E₀.veluY (E₀.oddOrderSummingSet Q n) x y) h')
    (C'' : AddSubgroup (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)).toAffine.Point)
    (hC'' : IsAddCyclic C'' ∧ Nat.card C'' = M) (hCC'' : ∀ T ∈ C, φ T ∈ C'') :
    (moduliPlace K (M * s) E₀ C).restrictAlong β hb =
      moduliPlace K M (E₀.veluQuotient (E₀.oddOrderSummingSet Q n)) C'' := by
  subst hs

  have hcurve : E₀.fullKernelQuotient Q (2 * n + 1) = E₀.veluQuotient (E₀.oddOrderSummingSet Q n) :=
    fullKernelQuotient_eq_veluQuotient_oddOrderSummingSet E₀ Q n hQ

  suffices key : ∀ (E' : WeierstrassCurve K) (hE : E₀.fullKernelQuotient Q (2 * n + 1) = E')
      (φ' : E₀.toAffine.Point →+ E'.toAffine.Point)
      (hker' : φ'.ker = AddSubgroup.zmultiples Q)
      (hφ' : ∀ P : E₀.toAffine.Point, P ∉ AddSubgroup.zmultiples Q →
        (φ' P).coordsOrZero =
          (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
              ((P + k • Q).coordsOrZero.1 - (k • Q).coordsOrZero.1),
           P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 * n + 1 - 1),
              ((P + k • Q).coordsOrZero.2 - (k • Q).coordsOrZero.2)))
      (hΔ' : E'.Δ ≠ 0) (C' : AddSubgroup E'.toAffine.Point)
      (hC' : IsAddCyclic C' ∧ Nat.card C' = M) (hφC' : ∀ T ∈ C, φ' T ∈ C'),
      (moduliPlace K (M * (2 * n + 1)) E₀ C).restrictAlong β hb = moduliPlace K M E' C' from
    key _ hcurve φ hφker (coordsOrZero_eq_translationSum E₀ Q n hQ φ hφ) hΔ C'' hC'' hCC''
  intro E' hE φ' hker' hφ' hΔ' C' hC' hφC'
  subst hE
  exact ModularCurve.moduliPlace_restrictAlong_qExpand_fullKernelQuotient K M (2 * n + 1) hMs huniq hex
    β hβ hb E₀ C hC Q hQC hQ hΔ' φ' hker' hφ' C' hC' hφC'

end S_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient
end P2MW
export P2MW.S_ModularCurve_moduliPlace_restrictAlong_qExpand_veluQuotient (solution)
