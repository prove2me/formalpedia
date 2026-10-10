-- Prove2me | solution 1 for MazurTransfer.order13_actual_quadratic_extension_field_points
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T12:13:31.863978+00:00
-- url     : https://prove2.me/submissions/a2e8da6c-38d3-44e6-add7-451a16069247

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
open AlgebraicGeometry CategoryTheory
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r) := ⟨by decide⟩
local instance : Fact (∀ r : ZMod 5, r ^ 2 ≠ (2 : ZMod 5) + 0 * r) := ⟨by decide⟩

section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Design boundary: exact reciprocal-chart overlap of the literal glued curve.
Named downstream consumer: its extension-field section-coordinate dictionary.
The mathematical declarations below are selected unchanged from the WIP
hyperelliptic-map source; only their namespace and imports are isolated.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory MazurTorsion
namespace MazurTransfer.Order13ChartOverlap
universe u
variable (K : Type u) [Field K]
private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private theorem reciprocalOrdinaryOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenProjectiveCurve.ReciprocalRing K)
          (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K))) := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        reciprocalOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem reciprocalGlueOverlap_opensRange :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg reciprocal_ne_ordinary]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage :
    reciprocalOverlapOpen K =
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm

theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage K).symm

end MazurTransfer.Order13ChartOverlap
#print axioms MazurTransfer.Order13ChartOverlap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen

end
end

section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Finite-field certificates for the `X₁(13)` sextic

This file records elementary certificates for the reductions modulo `3` and
`5` of

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

Both reduced sextics are separable: explicit Bézout coefficients for them and
their derivatives are checked in the kernel.  The affine solutions over
`ZMod 3` are exactly

`(0, 1), (0, -1), (-1, 1), (-1, -1)`.

For the usual weighted-projective compactification of a monic even-degree
hyperelliptic equation, the normalized infinity chart has equation `η² = 1`.
We define and enumerate those normalized directions, obtaining two of them.
The resulting sum type is only an explicit finite-field point *certificate*;
this file does not assert an equivalence with a projective-curve API.  We also
enumerate the same equation in transparent quadratic-algebra presentations
of `𝔽₉` and `𝔽₂₅`.  The nonsquare and inverse certificates for those
presentations are checked by `decide`, as are the point counts.

In particular, none of these calculations proves a classification over
`ℚ`, a theorem about the Jacobian, or injectivity of reduction on rational
points.
-/

namespace MazurTorsion.XOneThirteenFiniteField

open Polynomial

/-- The three-element residue field used for the order-thirteen point count. -/
abbrev F3 := ZMod 3

/-- The order-thirteen hyperelliptic sextic reduced modulo `3`. -/
noncomputable def sextic : Polynomial F3 :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- A computable presentation of the sextic's value function. -/
def sexticValue (x : F3) : F3 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- Evaluation of the reduced sextic agrees with the displayed formula. -/
lemma eval_sextic (x : F3) :
    Polynomial.eval x sextic = sexticValue x := by
  simp [sextic, sexticValue]

private lemma three_eq_zero : (3 : F3) = 0 := by decide

private lemma four_eq_one : (4 : F3) = 1 := by decide

private lemma five_eq_two : (5 : F3) = 2 := by decide

private lemma six_eq_zero : (6 : F3) = 0 := by decide

private lemma polynomial_four_eq_one : (4 : Polynomial F3) = 1 := by
  change C (4 : F3) = C 1
  rw [four_eq_one]

private lemma polynomial_three_eq_zero : (3 : Polynomial F3) = 0 := by
  rw [← C_ofNat (R := F3) 3, three_eq_zero, C_0]

private lemma polynomial_six_eq_zero : (6 : Polynomial F3) = 0 := by
  rw [← C_ofNat (R := F3) 6, six_eq_zero, C_0]

private lemma C_two_mul_two :
    C (2 : F3) * (2 : Polynomial F3) = 1 := by
  rw [← C_ofNat (R := F3) 2, ← C_mul]
  have h : (2 : F3) * 2 = 1 := by decide
  rw [h, C_1]

/-- The formal derivative of the reduced sextic. -/
lemma derivative_sextic :
    sextic.derivative = X ^ 4 + X ^ 3 + 1 := by
  simp [sextic, derivative_add, derivative_mul, derivative_pow]
  simp [three_eq_zero, four_eq_one, five_eq_two, six_eq_zero,
    polynomial_four_eq_one, polynomial_six_eq_zero]
  ring_nf
  calc
    C 2 * X ^ 4 * 2 =
        (C 2 * (2 : Polynomial F3)) * X ^ 4 := by ring
    _ = X ^ 4 := by rw [C_two_mul_two, one_mul]

/-- Left Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutLeft : Polynomial F3 :=
  X ^ 3 + 1

/-- Right Bézout coefficient for the sextic and its derivative. -/
noncomputable def bezoutRight : Polynomial F3 :=
  -(X ^ 5 + X ^ 4 + X)

/-- Explicit gcd certificate for the sextic and its derivative. -/
lemma sextic_derivative_bezout :
    bezoutLeft * sextic + bezoutRight * sextic.derivative = 1 := by
  rw [derivative_sextic]
  simp only [bezoutLeft, bezoutRight, sextic]
  ring_nf
  simp [polynomial_three_eq_zero, polynomial_six_eq_zero]

/-- The reduced sextic is coprime to its derivative. -/
theorem sextic_isCoprime_derivative :
    IsCoprime sextic sextic.derivative :=
  ⟨bezoutLeft, bezoutRight, sextic_derivative_bezout⟩

/-- The reduction modulo `3` is separable. -/
theorem sextic_separable : sextic.Separable :=
  sextic_isCoprime_derivative

/-- In particular, the reduced sextic is squarefree. -/
theorem sextic_squarefree : Squarefree sextic :=
  sextic_separable.squarefree

/-- The sextic and its derivative have no common root over `F3`. -/
theorem sextic_or_derivative_ne_zero (x : F3) :
    Polynomial.eval x sextic ≠ 0 ∨
      Polynomial.eval x sextic.derivative ≠ 0 := by
  by_contra h
  simp only [not_or, not_ne_iff] at h
  have heval :=
    congrArg (Polynomial.eval x) sextic_derivative_bezout
  simp [h.1, h.2] at heval

/-- An affine solution of the reduced hyperelliptic equation. -/
def AffineSolution :=
  {p : F3 × F3 // p.2 ^ 2 = sexticValue p.1}

instance : Fintype AffineSolution := by
  unfold AffineSolution
  infer_instance

/-- Complete enumeration of affine solutions over `F3`. -/
theorem affine_solution_iff :
    ∀ x y : F3,
      y ^ 2 = sexticValue x ↔
        (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
        (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  decide

/-- Polynomial-evaluation form of the complete affine enumeration. -/
theorem affine_solution_polynomial_iff (x y : F3) :
    y ^ 2 = Polynomial.eval x sextic ↔
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1)) := by
  rw [eval_sextic]
  exact affine_solution_iff x y

/-- There are exactly four affine solutions over `F3`. -/
theorem card_affineSolution :
    Fintype.card AffineSolution = 4 := by
  decide

/-- The two affine abscissas occurring modulo `3`.  They are precisely the
reductions of the rational affine cusp abscissas from the sextic model. -/
def IsAffineCuspX (x : F3) : Prop :=
  x = 0 ∨ x = -1

instance (x : F3) : Decidable (IsAffineCuspX x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = -1))

/-- Computable form of `affine_solution_is_cusp`. -/
theorem affine_solution_is_cusp_value :
    ∀ x y : F3,
      y ^ 2 = sexticValue x →
        IsAffineCuspX x := by
  decide

/-- Every affine `F3`-solution has a cusp abscissa. -/
theorem affine_solution_is_cusp :
    ∀ x y : F3,
      y ^ 2 = Polynomial.eval x sextic →
        IsAffineCuspX x := by
  intro x y h
  rw [eval_sextic] at h
  exact affine_solution_is_cusp_value x y h

/-- The affine equation has two ordinates over each cusp abscissa. -/
theorem cusp_abscissa_solution_iff :
    ∀ x : F3,
      IsAffineCuspX x →
        ∀ y : F3,
          y ^ 2 = sexticValue x ↔
            y = 1 ∨ y = -1 := by
  decide

/-- The derivative has the following computable value function. -/
lemma eval_derivative_sextic (x : F3) :
    Polynomial.eval x sextic.derivative =
      x ^ 4 + x ^ 3 + 1 := by
  rw [derivative_sextic]
  simp

/-- Explicit affine Jacobian certificate: at a solution, the two partial
derivatives `-f'(x)` and `2y` cannot both vanish. -/
theorem affine_jacobian_nonsingular :
    ∀ x y : F3,
      y ^ 2 = sexticValue x →
        x ^ 4 + x ^ 3 + 1 ≠ 0 ∨ 2 * y ≠ 0 := by
  decide

/-- Polynomial-evaluation form of the affine Jacobian certificate. -/
theorem affine_jacobian_nonsingular_polynomial
    (x y : F3)
    (hxy : y ^ 2 = Polynomial.eval x sextic) :
    Polynomial.eval x sextic.derivative ≠ 0 ∨ 2 * y ≠ 0 := by
  rw [eval_sextic] at hxy
  rw [eval_derivative_sextic]
  exact affine_jacobian_nonsingular x y hxy

/-- The reduced sextic is monic. -/
theorem sextic_monic : sextic.Monic := by
  simp only [sextic]
  monicity <;> norm_num

/-- A normalized direction in the infinity chart of the monic even-degree
model.  In weighted-projective coordinates these are the solutions with
`X = 1` and `Z = 0`. -/
def InfinityDirection :=
  {η : F3 // η ^ 2 = 1}

instance : Fintype InfinityDirection := by
  unfold InfinityDirection
  infer_instance

/-- The normalized equation `η² = 1` is exactly the leading-coefficient
equation for this monic sextic. -/
theorem infinity_equation_iff_leadingCoeff (η : F3) :
    η ^ 2 = 1 ↔ η ^ 2 = sextic.leadingCoeff := by
  rw [sextic_monic.leadingCoeff]

/-- Every normalized infinity direction satisfies the actual
leading-coefficient equation of the sextic. -/
theorem infinity_direction_satisfies_leadingCoeff
    (η : InfinityDirection) :
    η.1 ^ 2 = sextic.leadingCoeff :=
  (infinity_equation_iff_leadingCoeff η.1).mp η.property

/-- The normalized infinity directions are exactly `η = ±1`. -/
theorem infinity_direction_iff :
    ∀ η : F3,
      η ^ 2 = 1 ↔ η = 1 ∨ η = -1 := by
  decide

/-- There are exactly two normalized points in the infinity chart. -/
theorem card_infinityDirection :
    Fintype.card InfinityDirection = 2 := by
  decide

/-- The `Y`-partial derivative is nonzero at either infinity direction, so
the two normalized infinity-chart points are distinct smooth directions. -/
theorem infinity_direction_jacobian_nonsingular
    (η : InfinityDirection) :
    2 * η.1 ≠ 0 := by
  have heta :
      η.1 = 1 ∨ η.1 = -1 :=
    (infinity_direction_iff η.1).mp η.property
  rcases heta with heta | heta <;> rw [heta] <;> decide

/-- The elementary six-element certificate obtained by adjoining the two
normalized infinity directions to the four affine solutions.

No equivalence with a projective-curve implementation is claimed here. -/
def PointCertificate :=
  AffineSolution ⊕ InfinityDirection

instance : Fintype PointCertificate := by
  unfold PointCertificate
  infer_instance

/-- The affine enumeration plus the normalized infinity chart has six
elements. -/
theorem card_pointCertificate :
    Fintype.card PointCertificate = 6 := by
  change Fintype.card (AffineSolution ⊕ InfinityDirection) = 6
  rw [Fintype.card_sum]
  rw [card_affineSolution, card_infinityDirection]

/-! ## The second good prime -/

/-- The five-element residue field used for the second point count. -/
abbrev F5 := ZMod 5

/-- The order-thirteen hyperelliptic sextic reduced modulo `5`. -/
noncomputable def sexticF5 : Polynomial F5 :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- A computable presentation of the sextic's value function modulo `5`. -/
def sexticValueF5 (x : F5) : F5 :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

private lemma five_eq_zero_F5 : (5 : F5) = 0 := by decide

private lemma six_eq_one_F5 : (6 : F5) = 1 := by decide

private lemma polynomial_five_eq_zero_F5 :
    (5 : Polynomial F5) = 0 := by
  rw [← C_ofNat (R := F5) 5, five_eq_zero_F5, C_0]

private lemma polynomial_six_eq_one_F5 :
    (6 : Polynomial F5) = 1 := by
  rw [← C_ofNat (R := F5) 6, six_eq_one_F5, C_1]

private lemma polynomial_ten_eq_zero_F5 :
    (10 : Polynomial F5) = 0 := by
  have hten : (10 : F5) = 0 := by decide
  rw [← C_ofNat (R := F5) 10, hten, C_0]

private lemma C_five_eq_zero_F5 : C (5 : F5) = 0 := by
  rw [five_eq_zero_F5, C_0]

private lemma C_six_eq_one_F5 : C (6 : F5) = 1 := by
  rw [six_eq_one_F5, C_1]

private lemma C_three_mul_two_F5 :
    C (3 : F5) * (2 : Polynomial F5) = 1 := by
  rw [← C_ofNat (R := F5) 2, ← C_mul]
  have h : (3 : F5) * 2 = 1 := by decide
  rw [h, C_1]

/-- Evaluation of the reduced sextic modulo `5` agrees with the displayed
formula. -/
lemma eval_sexticF5 (x : F5) :
    Polynomial.eval x sexticF5 = sexticValueF5 x := by
  simp [sexticF5, sexticValueF5]

/-- The formal derivative of the sextic modulo `5`. -/
lemma derivative_sexticF5 :
    sexticF5.derivative = X ^ 5 + 4 * X ^ 3 + X ^ 2 + 2 * X + 4 := by
  simp [sexticF5, derivative_add, derivative_mul, derivative_pow]
  ring_nf
  rw [C_six_eq_one_F5, C_five_eq_zero_F5,
    polynomial_six_eq_one_F5]
  ring_nf
  calc
    X * C 2 + X ^ 2 * C 3 * 2 + X ^ 3 * C 4 + X ^ 5 =
        X ^ 5 + C 2 * X + (C 3 * (2 : Polynomial F5)) * X ^ 2 +
          C 4 * X ^ 3 := by ring
    _ = X ^ 5 + C 2 * X + X ^ 2 + C 4 * X ^ 3 := by
      rw [C_three_mul_two_F5]
      ring
    _ = X * 2 + X ^ 2 + X ^ 3 * 4 + X ^ 5 := by
      rw [← C_ofNat (R := F5) 2, ← C_ofNat (R := F5) 4]
      ring

/-- Left Bézout coefficient for the sextic modulo `5` and its derivative. -/
noncomputable def bezoutLeftF5 : Polynomial F5 :=
  -X ^ 3 + X ^ 2 - 2 * X + 2

/-- Right Bézout coefficient for the sextic modulo `5` and its derivative. -/
noncomputable def bezoutRightF5 : Polynomial F5 :=
  X ^ 4 + X ^ 3 + 2 * X ^ 2 - 2 * X + 1

/-- Explicit gcd certificate for the sextic modulo `5` and its derivative. -/
lemma sexticF5_derivative_bezout :
    bezoutLeftF5 * sexticF5 + bezoutRightF5 * sexticF5.derivative = 1 := by
  rw [derivative_sexticF5]
  simp only [bezoutLeftF5, bezoutRightF5, sexticF5]
  ring_nf
  simp [polynomial_five_eq_zero_F5, polynomial_six_eq_one_F5,
    polynomial_ten_eq_zero_F5]

/-- The reduction modulo `5` is separable. -/
theorem sexticF5_separable : sexticF5.Separable :=
  ⟨bezoutLeftF5, bezoutRightF5, sexticF5_derivative_bezout⟩

/-- An affine solution of the reduced equation over `𝔽₅`. -/
def AffineSolutionF5 :=
  {p : F5 × F5 // p.2 ^ 2 = sexticValueF5 p.1}

instance : Fintype AffineSolutionF5 := by
  unfold AffineSolutionF5
  infer_instance

/-- There are four affine solutions over `𝔽₅`. -/
theorem card_affineSolutionF5 :
    Fintype.card AffineSolutionF5 = 4 := by
  decide

/-- The normalized infinity directions over `𝔽₅`. -/
def InfinityDirectionF5 :=
  {η : F5 // η ^ 2 = 1}

instance : Fintype InfinityDirectionF5 := by
  unfold InfinityDirectionF5
  infer_instance

/-- There are two normalized infinity directions over `𝔽₅`. -/
theorem card_infinityDirectionF5 :
    Fintype.card InfinityDirectionF5 = 2 := by
  decide

/-- The six-element point certificate over `𝔽₅`. -/
def PointCertificateF5 :=
  AffineSolutionF5 ⊕ InfinityDirectionF5

instance : Fintype PointCertificateF5 := by
  unfold PointCertificateF5
  infer_instance

/-- The affine enumeration and infinity chart have six elements over `𝔽₅`. -/
theorem card_pointCertificateF5 :
    Fintype.card PointCertificateF5 = 6 := by
  change Fintype.card (AffineSolutionF5 ⊕ InfinityDirectionF5) = 6
  rw [Fintype.card_sum, card_affineSolutionF5, card_infinityDirectionF5]

/-! ## Quadratic extension certificates -/

/-- A transparent pair presentation of a quadratic algebra over `ZMod n`.
Multiplication below imposes `ω² = d`. -/
abbrev QuadraticPair (n : ℕ) := ZMod n × ZMod n

/-- Zero in the pair presentation. -/
def quadraticPairZero {n : ℕ} : QuadraticPair n :=
  (0, 0)

/-- One in the pair presentation. -/
def quadraticPairOne {n : ℕ} : QuadraticPair n :=
  (1, 0)

/-- Addition in the pair presentation. -/
def quadraticPairAdd {n : ℕ}
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 + v.1, u.2 + v.2)

/-- Multiplication in the pair presentation with `ω² = d`. -/
def quadraticPairMul {n : ℕ} (d : ZMod n)
    (u v : QuadraticPair n) : QuadraticPair n :=
  (u.1 * v.1 + d * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- Natural-number scalar multiplication in the pair presentation. -/
def quadraticPairNatScale {n : ℕ} (a : ℕ)
    (u : QuadraticPair n) : QuadraticPair n :=
  ((a : ZMod n) * u.1, (a : ZMod n) * u.2)

/-- Powers computed with the transparent quadratic multiplication. -/
def quadraticPairPow {n : ℕ} (d : ZMod n)
    (u : QuadraticPair n) : ℕ → QuadraticPair n
  | 0 => quadraticPairOne
  | k + 1 => quadraticPairMul d (quadraticPairPow d u k) u

/-- The sextic value in the pair presentation. -/
def quadraticPairSexticValue {n : ℕ} (d : ZMod n)
    (x : QuadraticPair n) : QuadraticPair n :=
  quadraticPairAdd (quadraticPairPow d x 6)
    (quadraticPairAdd
      (quadraticPairNatScale 2 (quadraticPairPow d x 5))
      (quadraticPairAdd (quadraticPairPow d x 4)
        (quadraticPairAdd
          (quadraticPairNatScale 2 (quadraticPairPow d x 3))
          (quadraticPairAdd
            (quadraticPairNatScale 6 (quadraticPairPow d x 2))
            (quadraticPairAdd (quadraticPairNatScale 4 x)
              quadraticPairOne)))))

/-- A quadratic-pair affine solution. -/
def QuadraticAffineSolution (n : ℕ) (d : ZMod n) :=
  {p : QuadraticPair n × QuadraticPair n //
    quadraticPairMul d p.2 p.2 = quadraticPairSexticValue d p.1}

/-- A normalized quadratic-pair infinity direction. -/
def QuadraticInfinityDirection (n : ℕ) (d : ZMod n) :=
  {η : QuadraticPair n //
    quadraticPairMul d η η = quadraticPairOne}

/-- The pair presentation of `𝔽₉`, using `ω² = 2`. -/
abbrev F9Pair := QuadraticPair 3

/-- Two is not a square in `𝔽₃`. -/
theorem two_not_square_F3 :
    ∀ a : F3, a ^ 2 ≠ 2 := by
  decide

/-- Every nonzero element in the nine-element pair presentation has a
multiplicative inverse.  Together with `two_not_square_F3`, this is a finite
certificate that the displayed quadratic algebra is the field `𝔽₉`. -/
theorem F9Pair_nonzero_has_mul_inverse :
    ∀ u : F9Pair, u ≠ quadraticPairZero →
      ∃ v : F9Pair,
        quadraticPairMul (2 : F3) u v = quadraticPairOne := by
  decide

instance : Fintype (QuadraticAffineSolution 3 (2 : F3)) := by
  unfold QuadraticAffineSolution QuadraticPair
  infer_instance

instance : Fintype (QuadraticInfinityDirection 3 (2 : F3)) := by
  unfold QuadraticInfinityDirection QuadraticPair
  infer_instance

/-- There are six affine solutions over the checked `𝔽₉` presentation. -/
theorem card_affineSolutionF9 :
    Fintype.card (QuadraticAffineSolution 3 (2 : F3)) = 6 := by
  decide

/-- There are two normalized infinity directions over the checked `𝔽₉`
presentation. -/
theorem card_infinityDirectionF9 :
    Fintype.card (QuadraticInfinityDirection 3 (2 : F3)) = 2 := by
  decide

/-- The point certificate over `𝔽₉`. -/
def PointCertificateF9 :=
  QuadraticAffineSolution 3 (2 : F3) ⊕
    QuadraticInfinityDirection 3 (2 : F3)

instance : Fintype PointCertificateF9 := by
  unfold PointCertificateF9
  infer_instance

/-- The quadratic-extension point certificate has eight elements over
`𝔽₉`. -/
theorem card_pointCertificateF9 :
    Fintype.card PointCertificateF9 = 8 := by
  change Fintype.card
    (QuadraticAffineSolution 3 (2 : F3) ⊕
      QuadraticInfinityDirection 3 (2 : F3)) = 8
  rw [Fintype.card_sum, card_affineSolutionF9, card_infinityDirectionF9]

/-- The pair presentation of `𝔽₂₅`, using `ω² = 2`. -/
abbrev F25Pair := QuadraticPair 5

/-- Two is not a square in `𝔽₅`. -/
theorem two_not_square_F5 :
    ∀ a : F5, a ^ 2 ≠ 2 := by
  decide

/-- Every nonzero element in the twenty-five-element pair presentation has
a multiplicative inverse. -/
theorem F25Pair_nonzero_has_mul_inverse :
    ∀ u : F25Pair, u ≠ quadraticPairZero →
      ∃ v : F25Pair,
        quadraticPairMul (2 : F5) u v = quadraticPairOne := by
  decide

instance : Fintype (QuadraticAffineSolution 5 (2 : F5)) := by
  unfold QuadraticAffineSolution QuadraticPair
  infer_instance

instance : Fintype (QuadraticInfinityDirection 5 (2 : F5)) := by
  unfold QuadraticInfinityDirection QuadraticPair
  infer_instance

/-- There are ten affine solutions over the checked `𝔽₂₅` presentation. -/
theorem card_affineSolutionF25 :
    Fintype.card (QuadraticAffineSolution 5 (2 : F5)) = 10 := by
  decide

/-- There are two normalized infinity directions over the checked
`𝔽₂₅` presentation. -/
theorem card_infinityDirectionF25 :
    Fintype.card (QuadraticInfinityDirection 5 (2 : F5)) = 2 := by
  decide

/-- The point certificate over `𝔽₂₅`. -/
def PointCertificateF25 :=
  QuadraticAffineSolution 5 (2 : F5) ⊕
    QuadraticInfinityDirection 5 (2 : F5)

instance : Fintype PointCertificateF25 := by
  unfold PointCertificateF25
  infer_instance

/-- The quadratic-extension point certificate has twelve elements over
`𝔽₂₅`. -/
theorem card_pointCertificateF25 :
    Fintype.card PointCertificateF25 = 12 := by
  change Fintype.card
    (QuadraticAffineSolution 5 (2 : F5) ⊕
      QuadraticInfinityDirection 5 (2 : F5)) = 12
  rw [Fintype.card_sum, card_affineSolutionF25,
    card_infinityDirectionF25]

/-- The two checked pairs of point counts.  For a smooth projective genus-two
curve these are the inputs `(#C(𝔽_q), #C(𝔽_{q²}))` to the standard
Jacobian-order formula.  This theorem only packages the finite enumerations;
it does not supply that geometric identification. -/
theorem twoPrime_pointCertificate_counts :
    (Fintype.card PointCertificate = 6 ∧
      Fintype.card PointCertificateF9 = 8) ∧
    (Fintype.card PointCertificateF5 = 6 ∧
      Fintype.card PointCertificateF25 = 12) := by
  exact ⟨⟨card_pointCertificate, card_pointCertificateF9⟩,
    ⟨card_pointCertificateF5, card_pointCertificateF25⟩⟩

/-! ## Degree-two divisor labels -/

/-- Labels for the six rational cusp points in either good reduction. -/
inductive RationalCuspLabel
  | zeroPos
  | zeroNeg
  | negOnePos
  | negOneNeg
  | infinityPos
  | infinityNeg
  deriving DecidableEq

instance : Fintype RationalCuspLabel where
  elems := {.zeroPos, .zeroNeg, .negOnePos, .negOneNeg,
    .infinityPos, .infinityNeg}
  complete x := by cases x <;> simp

/-- The ordering used to give unordered pairs a unique representative. -/
def rationalCuspLabelIndex : RationalCuspLabel → Fin 6
  | .zeroPos => 0
  | .zeroNeg => 1
  | .negOnePos => 2
  | .negOneNeg => 3
  | .infinityPos => 4
  | .infinityNeg => 5

/-- The hyperelliptic involution on rational cusp labels. -/
def rationalCuspConjugate : RationalCuspLabel → RationalCuspLabel
  | .zeroPos => .zeroNeg
  | .zeroNeg => .zeroPos
  | .negOnePos => .negOneNeg
  | .negOneNeg => .negOnePos
  | .infinityPos => .infinityNeg
  | .infinityNeg => .infinityPos

/-- The cusp label interpreted in the point certificate over `𝔽₃`. -/
def rationalCuspLabelPointF3 : RationalCuspLabel → PointCertificate
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse label for the `𝔽₃` point certificate. -/
def pointCertificateCuspLabelF3 : PointCertificate → RationalCuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers every rational cusp label over `𝔽₃`. -/
theorem pointCertificateCuspLabelF3_leftInverse :
    Function.LeftInverse pointCertificateCuspLabelF3
      rationalCuspLabelPointF3 := by
  intro c
  cases c <;> decide

/-- The six cusp labels enumerate the complete point certificate over `𝔽₃`. -/
theorem rationalCuspLabelPointF3_bijective :
    Function.Bijective rationalCuspLabelPointF3 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateCuspLabelF3_leftInverse.injective
  · rw [card_pointCertificate]
    decide

/-- The cusp label interpreted in the point certificate over `𝔽₅`. -/
def rationalCuspLabelPointF5 : RationalCuspLabel → PointCertificateF5
  | .zeroPos => .inl ⟨(0, 1), by decide⟩
  | .zeroNeg => .inl ⟨(0, -1), by decide⟩
  | .negOnePos => .inl ⟨(-1, 1), by decide⟩
  | .negOneNeg => .inl ⟨(-1, -1), by decide⟩
  | .infinityPos => .inr ⟨1, by decide⟩
  | .infinityNeg => .inr ⟨-1, by decide⟩

/-- A computational inverse label for the `𝔽₅` point certificate. -/
def pointCertificateCuspLabelF5 : PointCertificateF5 → RationalCuspLabel
  | .inl p =>
      if p.1.1 = 0 then
        if p.1.2 = 1 then .zeroPos else .zeroNeg
      else if p.1.2 = 1 then .negOnePos else .negOneNeg
  | .inr p =>
      if p.1 = 1 then .infinityPos else .infinityNeg

/-- The inverse label recovers every rational cusp label over `𝔽₅`. -/
theorem pointCertificateCuspLabelF5_leftInverse :
    Function.LeftInverse pointCertificateCuspLabelF5
      rationalCuspLabelPointF5 := by
  intro c
  cases c <;> decide

/-- The six cusp labels enumerate the complete point certificate over `𝔽₅`. -/
theorem rationalCuspLabelPointF5_bijective :
    Function.Bijective rationalCuspLabelPointF5 := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact pointCertificateCuspLabelF5_leftInverse.injective
  · rw [card_pointCertificateF5]
    decide

/-- An unordered pair of rational cusp labels, represented in increasing
index order. -/
def UnorderedRationalCuspPair :=
  {p : RationalCuspLabel × RationalCuspLabel //
    (rationalCuspLabelIndex p.1 : ℕ) ≤
      (rationalCuspLabelIndex p.2 : ℕ)}

instance : Fintype UnorderedRationalCuspPair := by
  unfold UnorderedRationalCuspPair
  infer_instance

/-- Six points have twenty-one unordered pairs with repetition. -/
theorem card_unorderedRationalCuspPair :
    Fintype.card UnorderedRationalCuspPair = 21 := by
  decide

/-- A rational cusp pair is a member of the hyperelliptic pencil when its
second label is the conjugate of its first. -/
def IsRationalHyperellipticPair
    (p : UnorderedRationalCuspPair) : Prop :=
  p.1.2 = rationalCuspConjugate p.1.1

instance (p : UnorderedRationalCuspPair) :
    Decidable (IsRationalHyperellipticPair p) := by
  unfold IsRationalHyperellipticPair
  infer_instance

/-- Exactly three rational unordered pairs are hyperelliptic fibers. -/
theorem card_rationalHyperellipticPair :
    Fintype.card {p : UnorderedRationalCuspPair //
      IsRationalHyperellipticPair p} = 3 := by
  decide

/-- Conjugation in the pair presentation. -/
def quadraticPairConjugate {n : ℕ}
    (u : QuadraticPair n) : QuadraticPair n :=
  (u.1, -u.2)

/-- Cubing in the checked nine-element presentation is pair conjugation. -/
theorem quadraticPairPow_three_eq_conjugate_F9 :
    ∀ u : F9Pair,
      quadraticPairPow (2 : F3) u 3 = quadraticPairConjugate u := by
  decide

/-- Fifth powering in the checked twenty-five-element presentation is pair
conjugation. -/
theorem quadraticPairPow_five_eq_conjugate_F25 :
    ∀ u : F25Pair,
      quadraticPairPow (2 : F5) u 5 = quadraticPairConjugate u := by
  decide

/-- A quadratic affine solution whose two coordinates do not both lie in
the base field. -/
def IsNonBaseQuadraticAffineSolution {n : ℕ} {d : ZMod n}
    (P : QuadraticAffineSolution n d) : Prop :=
  P.1.1.2 ≠ 0 ∨ P.1.2.2 ≠ 0

instance {n : ℕ} {d : ZMod n}
    (P : QuadraticAffineSolution n d) :
    Decidable (IsNonBaseQuadraticAffineSolution P) := by
  unfold IsNonBaseQuadraticAffineSolution
  infer_instance

/-- There are two non-base affine solutions over `𝔽₉`. -/
theorem card_nonBaseAffineSolutionF9 :
    Fintype.card {P : QuadraticAffineSolution 3 (2 : F3) //
      IsNonBaseQuadraticAffineSolution P} = 2 := by
  decide

/-- The non-base `𝔽₉` solutions form the fiber above the base-field
abscissa `1`, and their ordinates are genuinely quadratic. -/
theorem nonBaseAffineSolutionF9_abscissa :
    ∀ P : QuadraticAffineSolution 3 (2 : F3),
      IsNonBaseQuadraticAffineSolution P →
        P.1.1 = ((1, 0) : F9Pair) ∧ P.1.2.2 ≠ 0 := by
  decide

/-- At the non-base `𝔽₉` abscissa, the two ordinates are equal or
quadratic conjugates. -/
theorem nonBaseAffineSolutionF9_ordinates :
    ∀ P Q : QuadraticAffineSolution 3 (2 : F3),
      IsNonBaseQuadraticAffineSolution P →
      IsNonBaseQuadraticAffineSolution Q →
      P.1.1 = Q.1.1 →
        Q.1.2 = P.1.2 ∨ Q.1.2 = quadraticPairConjugate P.1.2 := by
  decide

/-- There are six non-base affine solutions over `𝔽₂₅`. -/
theorem card_nonBaseAffineSolutionF25 :
    Fintype.card {P : QuadraticAffineSolution 5 (2 : F5) //
      IsNonBaseQuadraticAffineSolution P} = 6 := by
  decide

/-- The non-base `𝔽₂₅` solutions lie above the three base-field
abscissas `1`, `2`, and `3`, with genuinely quadratic ordinates. -/
theorem nonBaseAffineSolutionF25_abscissa :
    ∀ P : QuadraticAffineSolution 5 (2 : F5),
      IsNonBaseQuadraticAffineSolution P →
        P.1.1.2 = 0 ∧
        (P.1.1.1 = 1 ∨ P.1.1.1 = 2 ∨ P.1.1.1 = 3) ∧
        P.1.2.2 ≠ 0 := by
  decide

/-- Above any of the three non-base `𝔽₂₅` abscissas, the two ordinates
are equal or quadratic conjugates. -/
theorem nonBaseAffineSolutionF25_ordinates :
    ∀ P Q : QuadraticAffineSolution 5 (2 : F5),
      IsNonBaseQuadraticAffineSolution P →
      IsNonBaseQuadraticAffineSolution Q →
      P.1.1 = Q.1.1 →
        Q.1.2 = P.1.2 ∨ Q.1.2 = quadraticPairConjugate P.1.2 := by
  decide

/-- The one quadratic closed fiber over `𝔽₃`, labeled by its base-field
abscissa. -/
def QuadraticClosedFiberF3 :=
  {x : F3 // x = 1}

instance : Fintype QuadraticClosedFiberF3 := by
  unfold QuadraticClosedFiberF3
  infer_instance

/-- There is one non-rational quadratic closed fiber over `𝔽₃`. -/
theorem card_quadraticClosedFiberF3 :
    Fintype.card QuadraticClosedFiberF3 = 1 := by
  decide

/-- The three quadratic closed fibers over `𝔽₅`, labeled by their
base-field abscissas. -/
def QuadraticClosedFiberF5 :=
  {x : F5 // x = 1 ∨ x = 2 ∨ x = 3}

instance : Fintype QuadraticClosedFiberF5 := by
  unfold QuadraticClosedFiberF5
  infer_instance

/-- There are three non-rational quadratic closed fibers over `𝔽₅`. -/
theorem card_quadraticClosedFiberF5 :
    Fintype.card QuadraticClosedFiberF5 = 3 := by
  decide

/-- Degree-two effective-divisor labels over `𝔽₃`: either an unordered
pair of rational points or the unique quadratic Frobenius orbit. -/
def DegreeTwoDivisorCertificateF3 :=
  UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF3

instance : Fintype DegreeTwoDivisorCertificateF3 := by
  unfold DegreeTwoDivisorCertificateF3
  infer_instance

/-- The degree-two certificate over `𝔽₃` has twenty-two elements. -/
theorem card_degreeTwoDivisorCertificateF3 :
    Fintype.card DegreeTwoDivisorCertificateF3 = 22 := by
  change Fintype.card
    (UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF3) = 22
  rw [Fintype.card_sum, card_unorderedRationalCuspPair,
    card_quadraticClosedFiberF3]

/-- Degree-two effective-divisor labels over `𝔽₅`. -/
def DegreeTwoDivisorCertificateF5 :=
  UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF5

instance : Fintype DegreeTwoDivisorCertificateF5 := by
  unfold DegreeTwoDivisorCertificateF5
  infer_instance

/-- The degree-two certificate over `𝔽₅` has twenty-four elements. -/
theorem card_degreeTwoDivisorCertificateF5 :
    Fintype.card DegreeTwoDivisorCertificateF5 = 24 := by
  change Fintype.card
    (UnorderedRationalCuspPair ⊕ QuadraticClosedFiberF5) = 24
  rw [Fintype.card_sum, card_unorderedRationalCuspPair,
    card_quadraticClosedFiberF5]

/-- The hyperelliptic-pencil labels among the degree-two certificates over
`𝔽₃`.  The quadratic closed fiber is one of those pencil members. -/
def IsCanonicalDegreeTwoF3 : DegreeTwoDivisorCertificateF3 → Prop
  | .inl p => IsRationalHyperellipticPair p
  | .inr _ => True

instance (D : DegreeTwoDivisorCertificateF3) :
    Decidable (IsCanonicalDegreeTwoF3 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPair p)
      exact inferInstance
  | inr _ => exact isTrue trivial

/-- The hyperelliptic pencil has four labels over `𝔽₃`. -/
theorem card_canonicalDegreeTwoF3 :
    Fintype.card {D : DegreeTwoDivisorCertificateF3 //
      IsCanonicalDegreeTwoF3 D} = 4 := by
  decide

/-- The hyperelliptic-pencil labels over `𝔽₅`. -/
def IsCanonicalDegreeTwoF5 : DegreeTwoDivisorCertificateF5 → Prop
  | .inl p => IsRationalHyperellipticPair p
  | .inr _ => True

instance (D : DegreeTwoDivisorCertificateF5) :
    Decidable (IsCanonicalDegreeTwoF5 D) := by
  cases D with
  | inl p =>
      change Decidable (IsRationalHyperellipticPair p)
      exact inferInstance
  | inr _ => exact isTrue trivial

/-- The hyperelliptic pencil has six labels over `𝔽₅`. -/
theorem card_canonicalDegreeTwoF5 :
    Fintype.card {D : DegreeTwoDivisorCertificateF5 //
      IsCanonicalDegreeTwoF5 D} = 6 := by
  decide

/-- The combinatorial reduced degree-two class certificate over `𝔽₃`:
retain every noncanonical divisor label and collapse the complete
hyperelliptic pencil to one distinguished label.

This is not defined to be a Picard group or a Jacobian. -/
def ReducedDegreeTwoClassCertificateF3 :=
  {D : DegreeTwoDivisorCertificateF3 // ¬ IsCanonicalDegreeTwoF3 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF3 := by
  unfold ReducedDegreeTwoClassCertificateF3
  infer_instance

/-- The reduced degree-two class certificate over `𝔽₃` has nineteen
elements. -/
theorem card_reducedDegreeTwoClassCertificateF3 :
    Fintype.card ReducedDegreeTwoClassCertificateF3 = 19 := by
  decide

/-- The analogous combinatorial reduced degree-two class certificate over
`𝔽₅`.  No Picard or Jacobian identification is asserted. -/
def ReducedDegreeTwoClassCertificateF5 :=
  {D : DegreeTwoDivisorCertificateF5 // ¬ IsCanonicalDegreeTwoF5 D} ⊕ Unit

instance : Fintype ReducedDegreeTwoClassCertificateF5 := by
  unfold ReducedDegreeTwoClassCertificateF5
  infer_instance

/-- The reduced degree-two class certificate over `𝔽₅` has nineteen
elements. -/
theorem card_reducedDegreeTwoClassCertificateF5 :
    Fintype.card ReducedDegreeTwoClassCertificateF5 = 19 := by
  decide

/-! ## A cyclic coordinate on the reduced class certificates -/

/-- A perfect six-element degree-two coordinate set in `ZMod 19`.  Opposite
labels are hyperelliptic conjugates. -/
def rationalCuspDegreeTwoCoordinate : RationalCuspLabel → ZMod 19
  | .zeroPos => 1
  | .zeroNeg => -1
  | .negOnePos => 7
  | .negOneNeg => -7
  | .infinityPos => 8
  | .infinityNeg => -8

/-- Hyperelliptic conjugation negates the cusp coordinate. -/
theorem rationalCuspDegreeTwoCoordinate_conjugate :
    ∀ c : RationalCuspLabel,
      rationalCuspDegreeTwoCoordinate (rationalCuspConjugate c) =
        -rationalCuspDegreeTwoCoordinate c := by
  intro c
  cases c <;> decide

/-- The coordinate of an unordered rational cusp pair. -/
def unorderedRationalCuspPairCoordinate
    (p : UnorderedRationalCuspPair) : ZMod 19 :=
  rationalCuspDegreeTwoCoordinate p.1.1 +
    rationalCuspDegreeTwoCoordinate p.1.2

/-- The degree-two class coordinate over `𝔽₃`.  A quadratic
hyperelliptic fiber has coordinate zero. -/
def degreeTwoClassCoordinateF3 :
    DegreeTwoDivisorCertificateF3 → ZMod 19
  | .inl p => unorderedRationalCuspPairCoordinate p
  | .inr _ => 0

/-- Vanishing of the `𝔽₃` coordinate detects exactly the canonical
hyperelliptic pencil. -/
theorem degreeTwoClassCoordinateF3_eq_zero_iff :
    ∀ D : DegreeTwoDivisorCertificateF3,
      degreeTwoClassCoordinateF3 D = 0 ↔ IsCanonicalDegreeTwoF3 D := by
  decide

/-- The degree-two class coordinate over `𝔽₅`. -/
def degreeTwoClassCoordinateF5 :
    DegreeTwoDivisorCertificateF5 → ZMod 19
  | .inl p => unorderedRationalCuspPairCoordinate p
  | .inr _ => 0

/-- Vanishing of the `𝔽₅` coordinate detects exactly the canonical
hyperelliptic pencil. -/
theorem degreeTwoClassCoordinateF5_eq_zero_iff :
    ∀ D : DegreeTwoDivisorCertificateF5,
      degreeTwoClassCoordinateF5 D = 0 ↔ IsCanonicalDegreeTwoF5 D := by
  decide

/-- The reduced coordinate over `𝔽₃`; the collapsed pencil is sent to
zero and every noncanonical divisor retains its nonzero coordinate. -/
def reducedDegreeTwoClassCoordinateF3 :
    ReducedDegreeTwoClassCertificateF3 → ZMod 19
  | .inl D => degreeTwoClassCoordinateF3 D.1
  | .inr _ => 0

/-- The reduced coordinate over `𝔽₃` is a bijection. -/
theorem reducedDegreeTwoClassCoordinateF3_bijective :
    Function.Bijective reducedDegreeTwoClassCoordinateF3 := by
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact (by decide :
      ∀ z : ZMod 19,
        ∃ D : ReducedDegreeTwoClassCertificateF3,
          reducedDegreeTwoClassCoordinateF3 D = z)
  · rw [card_reducedDegreeTwoClassCertificateF3, ZMod.card]

/-- The checked equivalence between the reduced `𝔽₃` certificate and the
nineteen cyclic coordinates. -/
noncomputable def reducedDegreeTwoClassEquivZModF3 :
    ReducedDegreeTwoClassCertificateF3 ≃ ZMod 19 :=
  Equiv.ofBijective reducedDegreeTwoClassCoordinateF3
    reducedDegreeTwoClassCoordinateF3_bijective

/-- Transport the cyclic group law along the checked `𝔽₃` coordinate.
This is a group law on the combinatorial certificate, not an assertion that
it is the geometric Jacobian. -/
noncomputable instance : AddCommGroup ReducedDegreeTwoClassCertificateF3 :=
  reducedDegreeTwoClassEquivZModF3.addCommGroup

/-- With the transported group law, the coordinate is an additive
equivalence to `ZMod 19`. -/
noncomputable def reducedDegreeTwoClassAddEquivZModF3 :
    ReducedDegreeTwoClassCertificateF3 ≃+ ZMod 19 :=
  reducedDegreeTwoClassEquivZModF3.addEquiv

/-- The reduced coordinate over `𝔽₅`. -/
def reducedDegreeTwoClassCoordinateF5 :
    ReducedDegreeTwoClassCertificateF5 → ZMod 19
  | .inl D => degreeTwoClassCoordinateF5 D.1
  | .inr _ => 0

/-- The reduced coordinate over `𝔽₅` is a bijection. -/
theorem reducedDegreeTwoClassCoordinateF5_bijective :
    Function.Bijective reducedDegreeTwoClassCoordinateF5 := by
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact (by decide :
      ∀ z : ZMod 19,
        ∃ D : ReducedDegreeTwoClassCertificateF5,
          reducedDegreeTwoClassCoordinateF5 D = z)
  · rw [card_reducedDegreeTwoClassCertificateF5, ZMod.card]

/-- The checked equivalence between the reduced `𝔽₅` certificate and
`ZMod 19`. -/
noncomputable def reducedDegreeTwoClassEquivZModF5 :
    ReducedDegreeTwoClassCertificateF5 ≃ ZMod 19 :=
  Equiv.ofBijective reducedDegreeTwoClassCoordinateF5
    reducedDegreeTwoClassCoordinateF5_bijective

/-- The transported cyclic group law on the `𝔽₅` certificate. -/
noncomputable instance : AddCommGroup ReducedDegreeTwoClassCertificateF5 :=
  reducedDegreeTwoClassEquivZModF5.addCommGroup

/-- The additive cyclic coordinate over `𝔽₅`. -/
noncomputable def reducedDegreeTwoClassAddEquivZModF5 :
    ReducedDegreeTwoClassCertificateF5 ≃+ ZMod 19 :=
  reducedDegreeTwoClassEquivZModF5.addEquiv

end MazurTorsion.XOneThirteenFiniteField

#print axioms MazurTorsion.XOneThirteenFiniteField.card_pointCertificate
#print axioms MazurTorsion.XOneThirteenFiniteField.card_pointCertificateF5

end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: literal sections Spec K -> C_R over Spec R for every field
extension K/R, identified with the affine equation and normalized infinity
directions. Named downstream consumer: the actual F9/F25 points of the F3/F5
curves and the ensuing degree-two place/divisor enumeration.
All morphisms retain their specified base map. No hypothesis of unique field
endomorphism, genus, Picard cardinality, rank, or reduction injectivity is used.
-/

noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory MazurTorsion
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ChartOverlap NeronModelInfra
namespace MazurTransfer.Order13ExtensionFieldSections
universe u
variable (R K : Type u) [Field R] [Field K] [Algebra R K]

def extensionBaseMap : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

def fieldPoint : Spec (.of K) := IsLocalRing.closedPoint K

private def algebraSectionEquiv (A : Type u) [CommRing A] [Algebra R A] :
    (A →ₐ[R] K) ≃ SchemeHomOver (extensionBaseMap R K)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) where
  toFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    unfold extensionBaseMap
    rw [← Spec.map_comp]
    apply Spec.map_inj.mpr
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap⟩
  invFun p := {
    __ := (Spec.preimage p.1).hom
    commutes' r := by
      have h : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage p.1 =
          CommRingCat.ofHom (algebraMap R K) := by
        apply Spec.map_inj.mp
        rw [Spec.map_comp, Spec.map_preimage]
        exact p.2
      exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of K => f.hom r) h }
  left_inv φ := by
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom φ.toRingHom))
  right_inv p := by apply Subtype.ext; exact Spec.map_preimage p.1

abbrev OrdinarySection := SchemeHomOver (extensionBaseMap R K) (ordinaryChartToBase R)
abbrev ReciprocalSection := SchemeHomOver (extensionBaseMap R K) (reciprocalChartToBase R)
abbrev ActualSection := SchemeHomOver (extensionBaseMap R K) (curveToBase R)
abbrev ReciprocalSolution :=
  {p : K × K // p.2 ^ 2 = aeval p.1 (reciprocalPolynomial R)}
abbrev InfinityDirection := {η : K // η ^ 2 = 1}

def ordinarySolutionEquivSection : Solution R K ≃ OrdinarySection R K :=
  (solutionEquivAlgHom K).trans (algebraSectionEquiv R K (CoordinateRing R))

def reciprocalSolutionToAlgHom (p : ReciprocalSolution R K) : ReciprocalRing R →ₐ[R] K :=
  AdjoinRoot.liftAlgHom (reciprocalEquation R) (aeval p.1.1) p.1.2 (by
    simpa [reciprocalEquation, Polynomial.aeval_def] using sub_eq_zero.mpr p.2)

@[simp] theorem reciprocalSolutionToAlgHom_z (p : ReciprocalSolution R K) :
    reciprocalSolutionToAlgHom R K p (zCoordinate R) = p.1.1 := by
  simp [reciprocalSolutionToAlgHom, zCoordinate]

@[simp] theorem reciprocalSolutionToAlgHom_w (p : ReciprocalSolution R K) :
    reciprocalSolutionToAlgHom R K p (wCoordinate R) = p.1.2 := by
  simp [reciprocalSolutionToAlgHom, wCoordinate]

def reciprocalAlgHomToSolution (φ : ReciprocalRing R →ₐ[R] K) : ReciprocalSolution R K :=
  ⟨(φ (zCoordinate R), φ (wCoordinate R)), by
    rw [← map_pow, wCoordinate_sq]
    simp [zCoordinate, Polynomial.aeval_def]⟩

def reciprocalSolutionEquivAlgHom : ReciprocalSolution R K ≃ (ReciprocalRing R →ₐ[R] K) where
  toFun := reciprocalSolutionToAlgHom R K
  invFun := reciprocalAlgHomToSolution R K
  left_inv p := by apply Subtype.ext; ext <;> simp [reciprocalAlgHomToSolution]
  right_inv φ := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [reciprocalSolutionToAlgHom, reciprocalAlgHomToSolution, zCoordinate]
    · simp [reciprocalSolutionToAlgHom, reciprocalAlgHomToSolution, wCoordinate]

def reciprocalSolutionEquivSection : ReciprocalSolution R K ≃ ReciprocalSection R K :=
  (reciprocalSolutionEquivAlgHom R K).trans (algebraSectionEquiv R K (ReciprocalRing R))

def infinitySolution (η : InfinityDirection K) : ReciprocalSolution R K :=
  ⟨(0, η.1), by simpa [reciprocalPolynomial] using η.2⟩

def ordinaryPoint (p : Solution R K) : ActualSection R K :=
  ⟨(ordinarySolutionEquivSection R K p).1 ≫ ordinaryChartMap R, by
    rw [Category.assoc, ordinaryChartMap_curveToBase]
    exact (ordinarySolutionEquivSection R K p).2⟩

def infinityPoint (η : InfinityDirection K) : ActualSection R K :=
  ⟨(reciprocalSolutionEquivSection R K (infinitySolution R K η)).1 ≫ reciprocalChartMap R, by
    rw [Category.assoc, reciprocalChartMap_curveToBase]
    exact (reciprocalSolutionEquivSection R K (infinitySolution R K η)).2⟩

def sectionFromCoordinates : Solution R K ⊕ InfinityDirection K → ActualSection R K
  | .inl p => ordinaryPoint R K p
  | .inr η => infinityPoint R K η

theorem reciprocal_point_in_ordinary_chart_iff (p : ReciprocalSolution R K) :
    ((reciprocalSolutionEquivSection R K p).1 ≫ reciprocalChartMap R)
      (fieldPoint K) ∈ Set.range (ordinaryChartMap R) ↔ p.1.1 ≠ 0 := by
  have hopen := reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen R
  change (reciprocalSolutionEquivSection R K p).1 (fieldPoint K) ∈
    reciprocalChartMap R ⁻¹ᵁ (ordinaryChartMap R).opensRange ↔ _
  rw [hopen]
  change PrimeSpectrum.comap (reciprocalSolutionToAlgHom R K p).toRingHom
    (fieldPoint K) ∈ PrimeSpectrum.basicOpen (zCoordinate R) ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change (reciprocalSolutionToAlgHom R K p) (zCoordinate R) ∉ IsLocalRing.maximalIdeal K ↔ _
  rw [reciprocalSolutionToAlgHom_z, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

theorem infinityPoint_not_in_ordinary_chart (η : InfinityDirection K) :
    (infinityPoint R K η).1 (fieldPoint K) ∉ Set.range (ordinaryChartMap R) := by
  change ((reciprocalSolutionEquivSection R K (infinitySolution R K η)).1 ≫
    reciprocalChartMap R) (fieldPoint K) ∉ _
  rw [reciprocal_point_in_ordinary_chart_iff]
  simp [infinitySolution]

theorem point_lifts_chart (p : Spec (.of K) ⟶ curveScheme R) :
    (∃ q : Spec (.of K) ⟶ XOneThirteenAffineCurve.scheme R, q ≫ ordinaryChartMap R = p) ∨
      ∃ q : Spec (.of K) ⟶ reciprocalScheme R, q ≫ reciprocalChartMap R = p := by
  obtain ⟨i, x, hx⟩ := (glueData R).ι_jointly_surjective (p (fieldPoint K))
  have hr : Set.range p ⊆ Set.range ((glueData R).ι i) := by
    rintro _ ⟨z, rfl⟩
    have hz : z = fieldPoint K := Subsingleton.elim _ _
    subst z
    exact ⟨x, hx⟩
  cases i
  · exact Or.inl ⟨IsOpenImmersion.lift (ordinaryChartMap R) p hr,
      IsOpenImmersion.lift_fac (ordinaryChartMap R) p hr⟩
  · exact Or.inr ⟨IsOpenImmersion.lift (reciprocalChartMap R) p hr,
      IsOpenImmersion.lift_fac (reciprocalChartMap R) p hr⟩

theorem sectionFromCoordinates_injective : Function.Injective (sectionFromCoordinates R K) := by
  intro p q h
  have hraw := congrArg Subtype.val h
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      apply congrArg Sum.inl
      apply (ordinarySolutionEquivSection R K).injective
      apply Subtype.ext
      exact (cancel_mono (ordinaryChartMap R)).mp hraw
    | inr η =>
      have hr : (infinityPoint R K η).1 (fieldPoint K) ∈ Set.range (ordinaryChartMap R) := by
        change (ordinaryPoint R K p).1 = (infinityPoint R K η).1 at hraw
        rw [← hraw]
        exact ⟨(ordinarySolutionEquivSection R K p).1 (fieldPoint K), rfl⟩
      exact False.elim (infinityPoint_not_in_ordinary_chart R K η hr)
  | inr η =>
    cases q with
    | inl q =>
      have hr : (infinityPoint R K η).1 (fieldPoint K) ∈ Set.range (ordinaryChartMap R) := by
        change (infinityPoint R K η).1 = (ordinaryPoint R K q).1 at hraw
        rw [hraw]
        exact ⟨(ordinarySolutionEquivSection R K q).1 (fieldPoint K), rfl⟩
      exact False.elim (infinityPoint_not_in_ordinary_chart R K η hr)
    | inr θ =>
      apply congrArg Sum.inr
      have he : infinitySolution R K η = infinitySolution R K θ :=
        (reciprocalSolutionEquivSection R K).injective
          (Subtype.ext ((cancel_mono (reciprocalChartMap R)).mp hraw))
      apply Subtype.ext
      exact congrArg (fun s : ReciprocalSolution R K => s.1.2) he

theorem sectionFromCoordinates_surjective : Function.Surjective (sectionFromCoordinates R K) := by
  classical
  intro p
  by_cases ho : p.1 (fieldPoint K) ∈ Set.range (ordinaryChartMap R)
  · have hr : Set.range p.1 ⊆ Set.range (ordinaryChartMap R) := by
      rintro _ ⟨z, rfl⟩
      have hz : z = fieldPoint K := Subsingleton.elim _ _
      subst z
      exact ho
    let q := IsOpenImmersion.lift (ordinaryChartMap R) p.1 hr
    have hq : q ≫ ordinaryChartMap R = p.1 := IsOpenImmersion.lift_fac _ _ hr
    let qs : OrdinarySection R K := ⟨q, by
      rw [← ordinaryChartMap_curveToBase, ← Category.assoc, hq]
      exact p.2⟩
    refine ⟨.inl ((ordinarySolutionEquivSection R K).symm qs), ?_⟩
    apply Subtype.ext
    change (ordinarySolutionEquivSection R K ((ordinarySolutionEquivSection R K).symm qs)).1 ≫
      ordinaryChartMap R = p.1
    rw [Equiv.apply_symm_apply]
    exact hq
  · obtain hordinary | ⟨q, hq⟩ := point_lifts_chart R K p.1
    · obtain ⟨q, hq⟩ := hordinary
      exact False.elim (ho ⟨q (fieldPoint K), congrArg (fun f => f (fieldPoint K)) hq⟩)
    let qs : ReciprocalSection R K := ⟨q, by
      rw [← reciprocalChartMap_curveToBase, ← Category.assoc, hq]
      exact p.2⟩
    let s := (reciprocalSolutionEquivSection R K).symm qs
    have he : (reciprocalSolutionEquivSection R K s).1 ≫ reciprocalChartMap R = p.1 := by
      dsimp [s]
      rw [Equiv.apply_symm_apply]
      exact hq
    have hz : s.1.1 = 0 := by
      by_contra hne
      apply ho
      rw [← he]
      exact (reciprocal_point_in_ordinary_chart_iff R K s).mpr hne
    have hy : s.1.2 ^ 2 = 1 := by
      have h := s.2
      simpa [hz, reciprocalPolynomial] using h
    let η : InfinityDirection K := ⟨s.1.2, hy⟩
    have hs : infinitySolution R K η = s := by
      apply Subtype.ext
      exact Prod.ext hz.symm rfl
    refine ⟨.inr η, ?_⟩
    apply Subtype.ext
    change (reciprocalSolutionEquivSection R K (infinitySolution R K η)).1 ≫ reciprocalChartMap R = p.1
    rw [hs]
    exact he

def actualExtensionFieldSectionEquiv :
    Solution R K ⊕ InfinityDirection K ≃ ActualSection R K :=
  Equiv.ofBijective (sectionFromCoordinates R K)
    ⟨sectionFromCoordinates_injective R K, sectionFromCoordinates_surjective R K⟩

end MazurTransfer.Order13ExtensionFieldSections
#print axioms MazurTransfer.Order13ExtensionFieldSections.actualExtensionFieldSectionEquiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine quadratic extension fields of orders nine and
twenty-five, with an exact dictionary to the unchanged WIP pair arithmetic.
Named downstream consumer: actual extension-field curve points and degree-two
place/divisor enumeration. Field structures come from the nonsquare
certificates and Mathlib's quadratic algebra, not a transported label group.
-/

noncomputable section
open Polynomial MazurTorsion
open MazurTorsion.XOneThirteenFiniteField MazurTorsion.XOneThirteenAffineCurve
namespace MazurTransfer.Order13QuadraticFields

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev Q (n : ℕ) (d : ZMod n) := QuadraticAlgebra (ZMod n) d 0
abbrev F9 := Q 3 2
abbrev F25 := Q 5 2

instance fieldF9 : Field F9 := by
  letI : Fact (∀ r : ZMod 3, r ^ 2 ≠ (2 : ZMod 3) + 0 * r) :=
    ⟨by simpa using two_not_square_F3⟩
  exact inferInstance

instance fieldF25 : Field F25 := by
  letI : Fact (∀ r : ZMod 5, r ^ 2 ≠ (2 : ZMod 5) + 0 * r) :=
    ⟨by simpa using two_not_square_F5⟩
  exact inferInstance

def pairEquiv (n : ℕ) (d : ZMod n) : Q n d ≃ QuadraticPair n :=
  QuadraticAlgebra.equivProd d 0

theorem card_F9 : Nat.card F9 = 9 := by
  rw [Nat.card_congr (pairEquiv 3 2), Nat.card_eq_fintype_card]
  simp [QuadraticPair, Fintype.card_prod, ZMod.card]

theorem card_F25 : Nat.card F25 = 25 := by
  rw [Nat.card_congr (pairEquiv 5 2), Nat.card_eq_fintype_card]
  simp [QuadraticPair, Fintype.card_prod, ZMod.card]

variable (n : ℕ) (d : ZMod n)

theorem pairEquiv_one : pairEquiv n d 1 = quadraticPairOne := rfl

theorem pairEquiv_add (x y : Q n d) :
    pairEquiv n d (x + y) = quadraticPairAdd (pairEquiv n d x) (pairEquiv n d y) := rfl

theorem pairEquiv_mul (x y : Q n d) :
    pairEquiv n d (x * y) = quadraticPairMul d (pairEquiv n d x) (pairEquiv n d y) := by
  apply Prod.ext <;> simp [pairEquiv, QuadraticAlgebra.equivProd, quadraticPairMul]

theorem pairEquiv_natScale (a : ℕ) (x : Q n d) :
    pairEquiv n d ((a : Q n d) * x) = quadraticPairNatScale a (pairEquiv n d x) := by
  apply Prod.ext <;> simp [pairEquiv, QuadraticAlgebra.equivProd, quadraticPairNatScale]

theorem pairEquiv_pow (x : Q n d) (a : ℕ) :
    pairEquiv n d (x ^ a) = quadraticPairPow d (pairEquiv n d x) a := by
  induction a with
  | zero => exact pairEquiv_one n d
  | succ a ih =>
    rw [pow_succ, pairEquiv_mul, ih]
    rfl

theorem pairEquiv_aeval_sextic (x : Q n d) :
    pairEquiv n d (aeval x (sexticPolynomial (ZMod n))) =
      quadraticPairSexticValue d (pairEquiv n d x) := by
  have h2 (y : Q n d) : pairEquiv n d (2 * y) =
      quadraticPairNatScale 2 (pairEquiv n d y) := by
    apply Prod.ext <;> simp [pairEquiv, QuadraticAlgebra.equivProd,
      quadraticPairNatScale, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have h4 (y : Q n d) : pairEquiv n d (4 * y) =
      quadraticPairNatScale 4 (pairEquiv n d y) := by
    apply Prod.ext <;> simp [pairEquiv, QuadraticAlgebra.equivProd,
      quadraticPairNatScale, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  have h6 (y : Q n d) : pairEquiv n d (6 * y) =
      quadraticPairNatScale 6 (pairEquiv n d y) := by
    apply Prod.ext <;> simp [pairEquiv, QuadraticAlgebra.equivProd,
      quadraticPairNatScale, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  simp only [sexticPolynomial, map_add, map_mul, map_pow, map_ofNat, aeval_X, map_one,
    add_assoc, pairEquiv_add, pairEquiv_pow, h2, h4, h6, pairEquiv_one,
    quadraticPairSexticValue]

def affineSolutionEquivCertificate :
    Solution (ZMod n) (Q n d) ≃ QuadraticAffineSolution n d where
  toFun p := ⟨(pairEquiv n d p.1.1, pairEquiv n d p.1.2), by
    rw [← pairEquiv_mul, ← pairEquiv_aeval_sextic]
    exact congrArg (pairEquiv n d) (by simpa [pow_two] using p.2)⟩
  invFun p := ⟨((pairEquiv n d).symm p.1.1, (pairEquiv n d).symm p.1.2), by
    apply (pairEquiv n d).injective
    rw [pow_two, pairEquiv_mul, pairEquiv_aeval_sextic]
    simpa only [Equiv.apply_symm_apply] using p.2⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext <;> simp
  right_inv p := by apply Subtype.ext; apply Prod.ext <;> simp

def infinityDirectionEquivCertificate :
    {η : Q n d // η ^ 2 = 1} ≃ QuadraticInfinityDirection n d where
  toFun η := ⟨pairEquiv n d η.1, by
    rw [← pairEquiv_mul, ← pairEquiv_one]
    exact congrArg (pairEquiv n d) (by simpa [pow_two] using η.2)⟩
  invFun η := ⟨(pairEquiv n d).symm η.1, by
    apply (pairEquiv n d).injective
    rw [pow_two, pairEquiv_mul, pairEquiv_one]
    simpa only [Equiv.apply_symm_apply] using η.2⟩
  left_inv η := by apply Subtype.ext; simp
  right_inv η := by apply Subtype.ext; simp

end MazurTransfer.Order13QuadraticFields
#print axioms MazurTransfer.Order13QuadraticFields.fieldF9
#print axioms MazurTransfer.Order13QuadraticFields.fieldF25
#print axioms MazurTransfer.Order13QuadraticFields.card_F9
#print axioms MazurTransfer.Order13QuadraticFields.card_F25
#print axioms MazurTransfer.Order13QuadraticFields.affineSolutionEquivCertificate
#print axioms MazurTransfer.Order13QuadraticFields.infinityDirectionEquivCertificate

end
end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual scheme-valued points of the literal F3/F5 curves
over their genuine quadratic extension fields. Named downstream consumer:
degree-two places and divisors, before computing the actual Picard group.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MazurTorsion
open MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13QuadraticExtensionPoints
open Order13ExtensionFieldSections Order13QuadraticFields
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def actualCertificateEquivNine :
    XOneThirteenFiniteField.PointCertificateF9 ≃ ActualSection (ZMod 3) F9 :=
  ((affineSolutionEquivCertificate 3 2).symm.sumCongr
    (infinityDirectionEquivCertificate 3 2).symm).trans
      (actualExtensionFieldSectionEquiv (ZMod 3) F9)

def actualCertificateEquivTwentyFive :
    XOneThirteenFiniteField.PointCertificateF25 ≃ ActualSection (ZMod 5) F25 :=
  ((affineSolutionEquivCertificate 5 2).symm.sumCongr
    (infinityDirectionEquivCertificate 5 2).symm).trans
      (actualExtensionFieldSectionEquiv (ZMod 5) F25)

theorem actual_extension_sections_mod_three_card :
    Nat.card (ActualSection (ZMod 3) F9) = 8 := by
  rw [← Nat.card_congr actualCertificateEquivNine, Nat.card_eq_fintype_card]
  exact XOneThirteenFiniteField.card_pointCertificateF9

theorem actual_extension_sections_mod_five_card :
    Nat.card (ActualSection (ZMod 5) F25) = 12 := by
  rw [← Nat.card_congr actualCertificateEquivTwentyFive, Nat.card_eq_fintype_card]
  exact XOneThirteenFiniteField.card_pointCertificateF25

end MazurTransfer.Order13QuadraticExtensionPoints
#print axioms MazurTransfer.Order13QuadraticExtensionPoints.actualCertificateEquivNine
#print axioms MazurTransfer.Order13QuadraticExtensionPoints.actualCertificateEquivTwentyFive
#print axioms MazurTransfer.Order13QuadraticExtensionPoints.actual_extension_sections_mod_three_card
#print axioms MazurTransfer.Order13QuadraticExtensionPoints.actual_extension_sections_mod_five_card

end
end

theorem solution.{u} :
    (∀ (R K : Type u) [Field R] [Field K] [Algebra R K],
      Nonempty ((MazurTorsion.XOneThirteenAffineCurve.Solution R K ⊕ {η : K // η ^ 2 = 1}) ≃
        NeronModelInfra.SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R))) ∧
    Nat.card (QuadraticAlgebra (ZMod 3) 2 0) = 9 ∧
    Nat.card (QuadraticAlgebra (ZMod 5) 2 0) = 25 ∧
    Nat.card (NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 3) (QuadraticAlgebra (ZMod 3) 2 0))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 3))) = 8 ∧
    Nat.card (NeronModelInfra.SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap (ZMod 5) (QuadraticAlgebra (ZMod 5) 2 0))))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase (ZMod 5))) = 12 := by
  refine ⟨?_, MazurTransfer.Order13QuadraticFields.card_F9,
    MazurTransfer.Order13QuadraticFields.card_F25,
    MazurTransfer.Order13QuadraticExtensionPoints.actual_extension_sections_mod_three_card,
    MazurTransfer.Order13QuadraticExtensionPoints.actual_extension_sections_mod_five_card⟩
  intro R K _ _ _
  exact ⟨MazurTransfer.Order13ExtensionFieldSections.actualExtensionFieldSectionEquiv R K⟩

#print axioms solution
