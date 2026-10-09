-- Prove2me | solution 1 for MazurProof.N13InfinityBaseChange.infinityCompatible
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:08:23.759403+00:00
-- url     : https://prove2.me/submissions/8e193fc7-a09b-4942-998b-aaf98e31c0ea

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_SexticMumford_OrientedBaseChange_nonZeroDivisors_le_comap
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13Infinity =====
section
/-!
# The positive infinity of the N13 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 6s² + 2s³ + s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `SexticMumford`.
-/
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
/-! ## The formal positive square root -/
theorem sqrtReverseF_sq : sqrtReverseF K ^ 2 = reverseF K := by
  let h := reverseTail_hasSubst K
  change (PowerSeries.substAlgHom h
      (PowerSeries.binomialSeries K (1 / 2 : K))) ^ 2 = reverseF K
  rw [pow_two, ← map_mul, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := by norm_num
  rw [hhalf]
  have hone : PowerSeries.binomialSeries K (1 : K) =
      (1 + PowerSeries.X : K⟦X⟧) := by
    simpa using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)
  rw [hone]
  simp only [map_add, map_one,
    PowerSeries.substAlgHom_X]
  simp [reverseTail]
/-! ## An algebraic model of the function field -/
/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/
omit [CharZero K] in
theorem reverseF_coe :
    ((reverseF K : K⟦X⟧) : LaurentSeries K) =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  simp [reverseF, parameter, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_pow, map_ofNat]
theorem wSeries_sq :
    wSeries K ^ 2 =
      1 + 4 * parameter K + 6 * parameter K ^ 2 +
        2 * parameter K ^ 3 + parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  rw [wSeries, ← PowerSeries.coe_pow, sqrtReverseF_sq, reverseF_coe]
end
end MazurProof.N13Infinity
end

end

-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13BranchNorm =====
section
/-!
# The two infinity branches and the quadratic norm on `X₁(13)`

For an affine function `p(X) + q(X)Y`, the two Laurent embeddings differ
only in the sign of `Y`.  Their product is therefore the polynomial norm
`p² - q²f`.  This packages the structural reason that the two infinity
orders must be used together: cancellation at one branch is detected by
the other branch.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13BranchNorm
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem coordinateToLaurent_yClass :
    N13Infinity.coordinateToLaurent K
      (SexticMumford.yClass (N13Mumford.model K)) =
      N13Infinity.ySeries K := by
  change N13Infinity.algebraicToLaurent K
    (N13Infinity.coordinateToAlgebraic K
      (AdjoinRoot.mk
        (SexticMumford.curvePoly (N13Mumford.model K)) X)) = _
  rw [N13Infinity.coordinateToAlgebraic_mk]
  simp only [Polynomial.map_X]
  exact AdjoinRoot.lift_root
    (N13Infinity.curvePolyRat_eval_ySeries K)
end
end MazurProof.N13BranchNorm
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordOrientedBaseChange =====
section
/-!
# Base change of oriented Picard classes for smooth sextics

An injective coefficient map carrying one sextic equation to another induces
maps on the affine coordinate rings, their fraction fields, and invertible
fractional ideals.  If the distinguished infinity orders are compatible,
the resulting map on oriented fractional ideals descends to an additive map
of the concrete oriented Picard groups.

The construction is algebraic: extension of fractional ideals and a quotient
universal property.  It does not use a relative Picard scheme.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford.OrientedBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K']
variable {M : Model K} {M' : Model K'}
@[simp] theorem coordinateMap_xClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) (p : K[X]) :
    coordinateMap ι hM (xClass M p) =
      xClass M' (p.map ι) := by
  exact AdjoinRoot.map_of
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM) p
@[simp] theorem coordinateMap_yClass
    (ι : K →+* K') (hM : M.f.map ι = M'.f) :
    coordinateMap ι hM (yClass M) = yClass M' := by
  exact AdjoinRoot.map_root
    (mapPoly ι) (curvePoly M) (curvePoly M')
      (target_curve_dvd ι hM)
@[simp] theorem functionMap_algebraMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (hM : M.f.map ι = M'.f) (z : CoordinateRing M) :
    functionMap ι hι hM
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M') (FunctionField M')
        (coordinateMap ι hM z) := by
  exact IsLocalization.map_eq
    (nonZeroDivisors_le_comap ι hι hM) z
end
end MazurProof.SexticMumford.OrientedBaseChange
end

end

-- ===== FLT.Assumptions.MazurProof.N13InfinityBaseChange =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13InfinityBaseChange =====
section
/-!
# Base change at the positive infinity of the N13 sextic

Coefficient extension commutes with the chosen positive Laurent branch of
the N13 function field.  The only apparent issue is the formal square root
used to define that branch.  We avoid coefficient calculations: after base
change the two candidate square roots have the same square and constant
coefficient `1`, so the factorization of a difference of squares excludes
the negative root.

For an injective coefficient map, coefficientwise extension of Laurent
series also preserves the support, hence its integer order.  Together these
facts give compatibility of the oriented infinity order and the induced
base-change map on concrete Picard groups.
-/
open Polynomial
open scoped LaurentSeries
namespace MazurProof.N13InfinityBaseChange
noncomputable section
universe u v
variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']
omit [CharZero K] [CharZero K'] in
theorem laurentMap_injective
    (ι : K →+* K') (hι : Function.Injective ι) :
    Function.Injective (laurentMap ι) := by
  intro z w h
  apply HahnSeries.coeff_injective
  funext n
  apply hι
  simpa only [laurentMap_coeff] using
    congrArg (fun q : LaurentSeries K' => q.coeff n) h
omit [CharZero K] [CharZero K'] in
theorem laurentMap_order
    (ι : K →+* K') (hι : Function.Injective ι)
    (z : LaurentSeries K) :
    (laurentMap ι z).order = z.order := by
  by_cases hz : z = 0
  · simp [hz]
  have hmz : laurentMap ι z ≠ 0 := by
    simpa using (laurentMap_injective ι hι).ne hz
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [laurentMap_coeff]
    simpa using
      hι.ne (HahnSeries.coeff_order_eq_zero.not.mpr hz)
  · apply HahnSeries.order_le_of_coeff_ne_zero
    intro hzero
    have :
        (laurentMap ι z).coeff (laurentMap ι z).order = 0 := by
      rw [laurentMap_coeff, hzero, map_zero]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hmz) this
omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_parameter
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.parameter K) =
      N13Infinity.parameter K' := by
  change
    ((HahnSeries.single (1 : ℤ) (1 : K)).map ι :
      LaurentSeries K') =
        HahnSeries.single (1 : ℤ) (1 : K')
  calc
    ((HahnSeries.single (1 : ℤ) (1 : K)).map ι :
        LaurentSeries K') =
        HahnSeries.single (1 : ℤ) (ι 1) :=
      HahnSeries.map_single (a := (1 : ℤ)) (r := (1 : K))
        ι.toZeroHom
    _ = HahnSeries.single (1 : ℤ) (1 : K') := by rw [map_one]
omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_algebraMap
    (ι : K →+* K') (a : K) :
    laurentMap ι (algebraMap K (LaurentSeries K) a) =
      algebraMap K' (LaurentSeries K') (ι a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  exact HahnSeries.map_single (a := (0 : ℤ)) (r := a)
    ι.toZeroHom
/-- The positive square root is natural under coefficient extension.

The proof uses its defining square and constant coefficient, rather than
expanding the binomial series coefficient by coefficient. -/
theorem laurentMap_wSeries
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.wSeries K) =
      N13Infinity.wSeries K' := by
  let a : LaurentSeries K' :=
    laurentMap ι (N13Infinity.wSeries K)
  let b : LaurentSeries K' :=
    N13Infinity.wSeries K'
  have hab_sq : a ^ 2 = b ^ 2 := by
    dsimp only [a, b]
    rw [← map_pow, N13Infinity.wSeries_sq,
      N13Infinity.wSeries_sq]
    simp only [map_add, map_mul, map_pow, map_one, map_ofNat,
      laurentMap_parameter]
  have hab_add_ne : a + b ≠ 0 := by
    intro hab
    have hcoeff := congrArg
      (fun z : LaurentSeries K' => z.coeff (0 : ℤ)) hab
    have ha_coeff :
        a.coeff (0 : ℤ) = 1 := by
      dsimp only [a]
      rw [laurentMap_coeff]
      unfold N13Infinity.wSeries
      rw [show (0 : ℤ) = (0 : ℕ) by rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rw [N13Infinity.sqrtReverseF_constantCoeff]
      exact map_one ι
    have hb_coeff :
        b.coeff (0 : ℤ) = 1 := by
      dsimp only [b]
      unfold N13Infinity.wSeries
      rw [show (0 : ℤ) = (0 : ℕ) by rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff]
      exact N13Infinity.sqrtReverseF_constantCoeff K'
    rw [HahnSeries.coeff_add, ha_coeff, hb_coeff,
      HahnSeries.coeff_zero] at hcoeff
    norm_num at hcoeff
  have hfactor : (a - b) * (a + b) = 0 := by
    calc
      (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hab_sq
  rcases mul_eq_zero.mp hfactor with hdiff | hsum
  · exact sub_eq_zero.mp hdiff
  · exact (hab_add_ne hsum).elim
@[simp] theorem laurentMap_ySeries
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.ySeries K) =
      N13Infinity.ySeries K' := by
  simp [N13Infinity.ySeries, N13InfinityBaseChange.laurentMap_wSeries]
omit [CharZero K] [CharZero K'] in
theorem eval_at_infinity_map
    (ι : K →+* K') (p : K[X]) :
    laurentMap ι
        (p.eval₂ (algebraMap K (LaurentSeries K))
          ((N13Infinity.parameter K)⁻¹)) =
      (p.map ι).eval₂ (algebraMap K' (LaurentSeries K'))
        ((N13Infinity.parameter K')⁻¹) := by
  have hcoeff :
      (laurentMap ι).comp
          (algebraMap K (LaurentSeries K)) =
        (algebraMap K' (LaurentSeries K')).comp ι := by
    apply RingHom.ext
    intro a
    exact laurentMap_algebraMap ι a
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map,
    hcoeff, map_inv₀, laurentMap_parameter]
/-- The affine positive-branch embedding commutes with N13 coefficient
extension. -/
theorem coordinateToLaurent_coordinateMap
    (ι : K →+* K') (z : N13Mumford.CoordinateRing K) :
    laurentMap ι (N13Infinity.coordinateToLaurent K z) =
      N13Infinity.coordinateToLaurent K'
        (SexticMumford.OrientedBaseChange.coordinateMap
          ι (map_n13_f ι) z) := by
  rw [← SexticMumford.recompose (N13Mumford.model K) z]
  simp only [map_add, map_mul,
    SexticMumford.OrientedBaseChange.coordinateMap_xClass,
    SexticMumford.OrientedBaseChange.coordinateMap_yClass,
    N13Infinity.coordinateToLaurent_xClass,
    N13BranchNorm.coordinateToLaurent_yClass]
  simp_rw [eval_at_infinity_map]
  rw [laurentMap_ySeries]
/-- The function-field positive-branch embedding commutes with coefficient
extension. -/
theorem functionFieldToLaurent_functionMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (z : N13Mumford.FunctionField K) :
    laurentMap ι (N13Infinity.functionFieldToLaurent K z) =
      N13Infinity.functionFieldToLaurent K'
        (SexticMumford.OrientedBaseChange.functionMap
          ι hι (map_n13_f ι) z) := by
  let lhs : N13Mumford.FunctionField K →+* LaurentSeries K' :=
    (laurentMap ι).comp
      (N13Infinity.functionFieldToLaurent K)
  let rhs : N13Mumford.FunctionField K →+* LaurentSeries K' :=
    (N13Infinity.functionFieldToLaurent K').comp
      (SexticMumford.OrientedBaseChange.functionMap
        ι hι (map_n13_f ι))
  have hhom : lhs = rhs := by
    apply IsFractionRing.ringHom_ext
      (A := N13Mumford.CoordinateRing K)
    intro w
    dsimp only [lhs, rhs, RingHom.comp_apply]
    rw [N13Infinity.functionFieldToLaurent_algebraMap,
      SexticMumford.OrientedBaseChange.functionMap_algebraMap,
      N13Infinity.functionFieldToLaurent_algebraMap,
      coordinateToLaurent_coordinateMap]
  change lhs z = rhs z
  rw [hhom]
/-- Every injective characteristic-zero coefficient extension preserves the
chosen positive infinity order on the N13 sextic. -/
theorem infinityCompatible
    (ι : K →+* K') (hι : Function.Injective ι) :
    SexticMumford.OrientedBaseChange.InfinityCompatible
      ι hι (map_n13_f ι)
      (N13Infinity.positiveInfinityOrder K)
      (N13Infinity.positiveInfinityOrder K') := by
  intro α
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K'
        (SexticMumford.OrientedBaseChange.functionMap
          ι hι (map_n13_f ι) (α : N13Mumford.FunctionField K))).order) =
    Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order)
  rw [← functionFieldToLaurent_functionMap ι hι,
    laurentMap_order ι hι]
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT
end
end MazurProof.N13InfinityBaseChange
end

end

theorem solution : type_of% @MazurProof.N13InfinityBaseChange.infinityCompatible := @MazurProof.N13InfinityBaseChange.infinityCompatible
