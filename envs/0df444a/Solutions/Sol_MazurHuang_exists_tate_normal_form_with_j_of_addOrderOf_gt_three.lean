-- Prove2me | solution 1 for MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:08:52.19366+00:00
-- url     : https://prove2.me/submissions/fd33d2a3-7367-4ebb-8169-1ca32e10c088

/-
Tate normal form for a rational point of order greater than three, with the j-invariant.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * scratch/TateZ2xZ10.lean
  * scratch/TateZ2xZ10Reduction.lean
  * FLT/Assumptions/MazurProof/TateNormalFormBridge.lean
  * the published statement
-/
import Mathlib

/- Source: flt@51bbb4f191ad scratch/TateZ2xZ10.lean (whole module, imports dropped). -/
section

/-!
# Algebraic core for the `Z/2 × Z/10` forward direction

This file only records the rational algebra after the Tate-normal-form
reduction.  The reduction from an arbitrary elliptic curve to these explicit
parameters is deliberately left to a later layer.
-/

def b10 (u : ℚ) : ℚ :=
  ((u - 1) ^ 3 * (u + 1)) / (u * (u ^ 2 - 4 * u - 1) ^ 2)

def c10 (u : ℚ) : ℚ :=
  ((u - 1) * (u + 1)) / (u * (u ^ 2 - 4 * u - 1))

def x5_10 (u : ℚ) : ℚ :=
  -((u - 1) ^ 3 * (u + 1)) / (4 * u ^ 2 * (u ^ 2 - 4 * u - 1))

def Q10 (u X : ℚ) : ℚ :=
  4 * X ^ 2
    - (8 * (u ^ 3 - 3 * u ^ 2 - u + 1) / (u ^ 2 - 4 * u - 1) ^ 2) * X
    + 4 * (u - 1) ^ 3 * (u + 1) / (u ^ 2 - 4 * u - 1) ^ 3

def w10 (u xT : ℚ) : ℚ :=
  ((u ^ 2 - 4 * u - 1) ^ 2 * xT - (u ^ 3 - 3 * u ^ 2 - u + 1)) / 2

private lemma rat_sq_ne_five (r : ℚ) : r ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨r, by simpa [pow_two] using h.symm⟩
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot hsq

lemma u2_sub_4u_sub_1_ne_zero (u : ℚ) : u ^ 2 - 4 * u - 1 ≠ 0 := by
  intro h
  exact rat_sq_ne_five (u - 2) (by nlinarith)

private lemma w10_sq_sub_E20_poly (u xT : ℚ) :
    w10 u xT ^ 2 - (u ^ 3 + u ^ 2 - u) =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 4) * xT ^ 2
        - ((u ^ 2 - 4 * u - 1) ^ 2 * (u ^ 3 - 3 * u ^ 2 - u + 1) * xT) / 2
        + ((u ^ 2 - 4 * u - 1) * ((u - 1) ^ 3 * (u + 1))) / 4 := by
  unfold w10
  ring

private lemma scaled_Q10_eq_poly_aux (D A B X : ℚ) (hD : D ≠ 0) :
    (D ^ 4 / 16) * (4 * X ^ 2 - (8 * A / D ^ 2) * X + 4 * B / D ^ 3) =
      (D ^ 4 / 4) * X ^ 2 - (D ^ 2 * A * X) / 2 + (D * B) / 4 := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  field_simp [hD, hD2, hD3]
  ring

private lemma scaled_Q10_eq_poly (u xT : ℚ) (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) :
    ((u ^ 2 - 4 * u - 1) ^ 4 / 16) * Q10 u xT =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 4) * xT ^ 2
        - ((u ^ 2 - 4 * u - 1) ^ 2 * (u ^ 3 - 3 * u ^ 2 - u + 1) * xT) / 2
        + ((u ^ 2 - 4 * u - 1) * ((u - 1) ^ 3 * (u + 1))) / 4 := by
  unfold Q10
  simpa [mul_assoc] using scaled_Q10_eq_poly_aux (u ^ 2 - 4 * u - 1)
    (u ^ 3 - 3 * u ^ 2 - u + 1) ((u - 1) ^ 3 * (u + 1)) xT hu2

lemma w10_sq_sub_E20 (u xT : ℚ) (hu : u ≠ 0) (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) :
    w10 u xT ^ 2 - (u ^ 3 + u ^ 2 - u) =
      ((u ^ 2 - 4 * u - 1) ^ 4 / 16) * Q10 u xT := by
  have _hu := hu
  rw [w10_sq_sub_E20_poly u xT, scaled_Q10_eq_poly u xT hu2]

lemma E20_point_of_Q10_root (u xT : ℚ) (hu : u ≠ 0)
    (hu2 : u ^ 2 - 4 * u - 1 ≠ 0) (hQ : Q10 u xT = 0) :
    (w10 u xT) ^ 2 = u ^ 3 + u ^ 2 - u := by
  have h := w10_sq_sub_E20 u xT hu hu2
  rw [hQ, mul_zero] at h
  nlinarith

end

/- Source: flt@51bbb4f191ad scratch/TateZ2xZ10Reduction.lean (whole module, imports dropped). -/
section

/-!
# Tate-normal-form reduction layer for `ZMod 2 × ZMod 10`

This file builds the forward-direction reduction up to the current formal wall.

API survey, from the local tree and Mathlib as used here:

* Nonzero affine coordinates.  `WeierstrassCurve.Affine.Point W` is the
  inductive type `zero | some x y h`.  Mathlib provides `Point.mk`,
  `Point.some_ne_zero`, and `Point.xRep`; there is no `Point.pointEquiv` in the
  local Mathlib checkout.  No extra abstraction is needed to extract `(x,y)`
  from a proof `P ≠ 0`: case-splitting on `P` gives the affine coordinates.

* Variable changes.  `WeierstrassCurve.VariableChange R` exists and acts on
  Weierstrass curves by `(X,Y) ↦ (u^2 X + r, u^3 Y + u^2 s X + t)`.  The hard
  Mathlib survey for this file found the following.

  * `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` provides the
    curve-level group action, coefficient formulas `variableChange_a₁` through
    `variableChange_a₆`, preservation of `IsElliptic`, base-change compatibility
    for variable changes, and `variableChange_j`.
  * `Affine.Basic` provides ring-hom/base-change transport for equations and
    nonsingularity, plus only a specialized
    `equation_iff_variableChange`/`nonsingular_iff_variableChange` for translating
    a point to `(0,0)`.  It does not provide a general point map for
    `(u,r,s,t)`.
  * `Affine.Point` provides `Point.map` only for base change along algebra
    homomorphisms; its `map_add'` proof uses the affine addition formulas under
    ring homs.  There is no `Point.mapEquiv`, `Affine.map`, or `≃+` for
    variable changes.
  * `Jacobian.Point` provides `toAffineAddEquiv` between Jacobian and affine
    point groups and base-change lemmas for Jacobian formulas, but no
    `VariableChange` action on Jacobian/projective point classes.
  * `IsomOfJ.lean` constructs curve-level variable changes from equal
    `j`-invariants; it does not construct point-group isomorphisms.

  Consequently the point-level transport below is built directly.  The forward
  map sends an old affine point `(x,y)` on `W` to the new coordinates
  `X = u^{-2}(x-r)`, `Y = u^{-3}(y-s(x-r)-t)` on `C • W`; the inverse map uses
  the defining coordinate formulas.  The additive proof reduces to the affine
  slope identity `ℓ' = u^{-1}(ℓ-s)` and ring-checked equivariance of `addX` and
  `addY`.

* Computing `n • P`.  The affine point file has explicit group-law lemmas:
  `Point.add_of_X_ne`, `Point.add_of_Y_eq`, `Point.add_self_of_Y_eq`,
  `Point.add_self_of_Y_ne`, and the underlying formulas `slope`, `addX`,
  `addY`.  This supports direct coordinate calculations, as in the existing
  obstruction files.  Mathlib does not provide Tate normal form, Kubert's
  order-10 table, or a canned theorem that a point of order `10` can be
  normalized to `(0,0)` with the roadmap's `b,c` formulas.

* Division polynomials.  `DivisionPolynomial/Basic.lean` defines
  `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ`, `ΨSq`, `Ψ`, `ψ`, `Φ`, and `φ`, with
  map/base-change lemmas; `DivisionPolynomial/Degree.lean` proves degree and
  leading-coefficient facts.  The only direct bridge to the 2-torsion cubic is
  `Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly`.  The survey found no
  theorem connecting `P` satisfying `n • P = 0` or `addOrderOf P = n` to
  evaluating `ψ n`, `Ψ n`, `preΨ n`, or `Φ n` at the coordinates of `P`.
  Thus division polynomials do not currently avoid the explicit `5P`
  group-law computation needed for order `10`.

The proven content below is split accordingly:

* the pure finite-group extraction from an injective `ZMod 2 × ZMod 10`;
* raw Tate-normal-form and change-of-variable algebra;
* one precisely named helper marking the missing point-level group-law
  preservation/normalization theorem.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The Tate normal form `y^2 + (1-c)xy - by = x^3 - bx^2`. -/
def tateNormalFormCurve (b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

@[simp] lemma tateNormalFormCurve_a₁ (b c : ℚ) :
    (tateNormalFormCurve b c).a₁ = 1 - c := rfl

@[simp] lemma tateNormalFormCurve_a₂ (b c : ℚ) :
    (tateNormalFormCurve b c).a₂ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₃ (b c : ℚ) :
    (tateNormalFormCurve b c).a₃ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₄ (b c : ℚ) :
    (tateNormalFormCurve b c).a₄ = 0 := rfl

@[simp] lemma tateNormalFormCurve_a₆ (b c : ℚ) :
    (tateNormalFormCurve b c).a₆ = 0 := rfl

/-- The order-10 Tate condition from the roadmap. -/
def Phi10 (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c
    + b * c ^ 4 + 3 * b * c ^ 3 + b * c ^ 2 + c ^ 5

/-- The two-torsion cubic specialized to Tate normal form. -/
def tateTwoTorsionCubic (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

lemma tate_linear_relation_of_two_torsion
    {b c x y : ℚ} [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    {h : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x y}
    (h2 : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0) :
    2 * y + (1 - c) * x - b = 0 := by
  have h2add :
      (WeierstrassCurve.Affine.Point.some x y h :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) +
        WeierstrassCurve.Affine.Point.some x y h = 0 := by
    simpa [two_nsmul] using h2
  have hy : y = WeierstrassCurve.Affine.negY (tateNormalFormCurve b c) x y := by
    by_contra hy
    have hs :
        (WeierstrassCurve.Affine.Point.some x y h :
            WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) +
          WeierstrassCurve.Affine.Point.some x y h =
            WeierstrassCurve.Affine.Point.some _ _
              (WeierstrassCurve.Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
    rw [h2add] at hs
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hs.symm
  rw [WeierstrassCurve.Affine.negY] at hy
  simp [tateNormalFormCurve] at hy
  nlinarith

lemma tate_cubic_of_two_torsion
    {b c x y : ℚ} [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    {h : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x y}
    (h2 : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0) :
    tateTwoTorsionCubic b c x = 0 := by
  have h2add :
      (WeierstrassCurve.Affine.Point.some x y h :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) +
        WeierstrassCurve.Affine.Point.some x y h = 0 := by
    simpa [two_nsmul] using h2
  have heq : WeierstrassCurve.Affine.Equation (tateNormalFormCurve b c) x y := h.1
  have hrel := tate_linear_relation_of_two_torsion
    (b := b) (c := c) (x := x) (y := y) (h := h) h2
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  unfold tateTwoTorsionCubic at *
  simp at heq hrel ⊢
  nlinarith

lemma tate_two_torsion_x_ne_of_point_ne
    {b c x₁ y₁ x₂ y₂ : ℚ} [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    {h₁ : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x₁ y₁}
    {h₂ : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x₂ y₂}
    (ht₁ : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0)
    (ht₂ : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0)
    (hne :
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ :
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) ≠
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) :
    x₁ ≠ x₂ := by
  intro hx
  apply hne
  have hr₁ := tate_linear_relation_of_two_torsion
    (b := b) (c := c) (x := x₁) (y := y₁) (h := h₁) ht₁
  have hr₂ := tate_linear_relation_of_two_torsion
    (b := b) (c := c) (x := x₂) (y := y₂) (h := h₂) ht₂
  subst x₂
  have hy : y₁ = y₂ := by nlinarith
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, hy⟩

/-- The rational `u` parameter recovered from Tate parameters `b,c`. -/
def uOfTateParameters (b c : ℚ) : ℚ :=
  (5 * b ^ 2 - 2 * b * c ^ 2 - 6 * b * c - 2 * c ^ 3 + c ^ 2) / (b - c) ^ 2

/-- Tangent slope at `(x₀,y₀)` in a general Weierstrass equation. -/
def tangentSlope (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) : ℚ :=
  (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀)
    / (2 * y₀ + W.a₁ * x₀ + W.a₃)

/-- The translation/shear sending `(x₀,y₀)` to `(0,0)` with tangent `Y=0`. -/
def translateToOriginTangent (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := x₀
  s := tangentSlope W x₀ y₀
  t := y₀

@[simp] lemma translateToOriginTangent_a₁ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₁ =
      W.a₁ + 2 * tangentSlope W x₀ y₀ := by
  rw [WeierstrassCurve.variableChange_a₁]
  simp [translateToOriginTangent]

@[simp] lemma translateToOriginTangent_a₂ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₂ =
      W.a₂ - tangentSlope W x₀ y₀ * W.a₁ + 3 * x₀ - tangentSlope W x₀ y₀ ^ 2 := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [translateToOriginTangent]

@[simp] lemma translateToOriginTangent_a₃ (W : WeierstrassCurve ℚ) (x₀ y₀ : ℚ) :
    ((translateToOriginTangent W x₀ y₀) • W).a₃ =
      W.a₃ + W.a₁ * x₀ + 2 * y₀ := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [translateToOriginTangent]
  ring

/-- If `(x₀,y₀)` lies on `W`, the translated curve has constant term zero. -/
lemma translateToOriginTangent_a₆_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hP : WeierstrassCurve.Affine.Equation W x₀ y₀) :
    ((translateToOriginTangent W x₀ y₀) • W).a₆ = 0 := by
  rw [WeierstrassCurve.variableChange_a₆]
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  simp [translateToOriginTangent]
  nlinarith

/-- If the point is not 2-torsion, the tangent choice kills the linear `X` term. -/
lemma translateToOriginTangent_a₄_eq_zero
    (W : WeierstrassCurve ℚ) {x₀ y₀ : ℚ}
    (hden : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0) :
    ((translateToOriginTangent W x₀ y₀) • W).a₄ = 0 := by
  have hs :
      tangentSlope W x₀ y₀ * (2 * y₀ + W.a₁ * x₀ + W.a₃) =
        3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ - W.a₁ * y₀ := by
    unfold tangentSlope
    exact div_mul_cancel₀ _ hden
  rw [WeierstrassCurve.variableChange_a₄]
  simp [translateToOriginTangent]
  linear_combination -hs

/-- Scaling `X = ρ^2 X'`, `Y = ρ^3 Y'`. -/
def scaleByRho (ρ : ℚ) (hρ : ρ ≠ 0) : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 ρ hρ
  r := 0
  s := 0
  t := 0

lemma scaleByRho_a₂ (W : WeierstrassCurve ℚ) (ρ : ℚ) (hρ : ρ ≠ 0) :
    ((scaleByRho ρ hρ) • W).a₂ = W.a₂ / ρ ^ 2 := by
  rw [WeierstrassCurve.variableChange_a₂]
  simp [scaleByRho, div_eq_mul_inv, inv_pow]
  ring

lemma scaleByRho_a₃ (W : WeierstrassCurve ℚ) (ρ : ℚ) (hρ : ρ ≠ 0) :
    ((scaleByRho ρ hρ) • W).a₃ = W.a₃ / ρ ^ 3 := by
  rw [WeierstrassCurve.variableChange_a₃]
  simp [scaleByRho, div_eq_mul_inv, inv_pow]
  ring

lemma scaleByTateRho_a₂
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₂ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleByRho_a₂]
  field_simp [ha₂, ha₃]

lemma scaleByTateRho_a₃
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ ≠ 0) (ha₃ : W.a₃ ≠ 0) :
    ((scaleByRho (W.a₃ / W.a₂) (div_ne_zero ha₃ ha₂)) • W).a₃ =
      W.a₂ ^ 3 / W.a₃ ^ 2 := by
  rw [scaleByRho_a₃]
  field_simp [ha₂, ha₃]

/-- Tate `b` after the roadmap's scaling step. -/
def tateBFromCoefficients (a₂' a₃' : ℚ) : ℚ :=
  -a₂' ^ 3 / a₃' ^ 2

/-- Tate `c` after the roadmap's scaling step. -/
def tateCFromCoefficients (a₁' a₂' a₃' : ℚ) : ℚ :=
  1 - a₁' * a₂' / a₃'

/-- The transformed `x`-coordinate of an auxiliary point under the scaling step. -/
def scaledAuxiliaryX (xTold x₀ ρ : ℚ) : ℚ :=
  (xTold - x₀) / ρ ^ 2

lemma Phi10_b10_c10_eq_zero (u : ℚ) (hu : u ≠ 0)
    (_hD : u ^ 2 - 4 * u - 1 ≠ 0) :
    Phi10 (b10 u) (c10 u) = 0 := by
  unfold Phi10 b10 c10
  field_simp [hu, _hD]
  ring

private def reverseUNum (b c : ℚ) : ℚ :=
  5 * b ^ 2 - 2 * b * c ^ 2 - 6 * b * c - 2 * c ^ 3 + c ^ 2

private def reverseUDen (b c : ℚ) : ℚ :=
  (b - c) ^ 2

private def reverseDNum (b c : ℚ) : ℚ :=
  reverseUNum b c ^ 2 - 4 * reverseUNum b c * reverseUDen b c - reverseUDen b c ^ 2

private def uNumBezoutA (b c : ℚ) : ℚ :=
  -4 * c ^ 3 + 11 * c ^ 4 - 13 * c ^ 5 - 2 * c ^ 6
    + b * (20 * c ^ 2 + 5 * c ^ 3 + 5 * c ^ 4)

private def uNumBezoutB (b c : ℚ) : ℚ :=
  4 * c ^ 6 - 7 * c ^ 7 - c ^ 8
    + b * (4 * c ^ 3 + 9 * c ^ 4 + 6 * c ^ 5 + 3 * c ^ 6)
    + b ^ 2 * (-4 * c ^ 2 - c ^ 3 - c ^ 4)

private lemma c_pow_nine_of_Phi10_and_reverseUNum_eq_zero
    (b c : ℚ) (hΦ : Phi10 b c = 0) (hN : reverseUNum b c = 0) :
    c ^ 9 = 0 := by
  have hcomb :
      uNumBezoutA b c * Phi10 b c + uNumBezoutB b c * reverseUNum b c =
        -4 * c ^ 9 := by
    simp only [uNumBezoutA, uNumBezoutB, reverseUNum, Phi10]
    ring_nf
  rw [hΦ, hN] at hcomb
  nlinarith

private lemma uOfTateParameters_ne_zero_of_Phi10
    (b c : ℚ) (hc : c ≠ 0) (hbc : b - c ≠ 0) (hΦ : Phi10 b c = 0) :
    uOfTateParameters b c ≠ 0 := by
  intro hu
  have hden : (b - c) ^ 2 ≠ 0 := pow_ne_zero 2 hbc
  have hN : reverseUNum b c = 0 := by
    unfold uOfTateParameters at hu
    rw [div_eq_zero_iff] at hu
    rcases hu with hnum | hden0
    · simpa [reverseUNum] using hnum
    · exact False.elim (hden hden0)
  have hc9 : c ^ 9 = 0 := c_pow_nine_of_Phi10_and_reverseUNum_eq_zero b c hΦ hN
  have hc0 : c = 0 := (pow_eq_zero_iff (by norm_num : (9 : ℕ) ≠ 0)).mp hc9
  exact hc hc0

private def reverseBQuotient (b c : ℚ) : ℚ :=
  128 * b ^ 2 * c ^ 5 - 896 * b ^ 3 * c ^ 4 + 2304 * b ^ 4 * c ^ 3
    - 2816 * b ^ 5 * c ^ 2 + 1664 * b ^ 6 * c - 384 * b ^ 7
    + 16 * c ^ 8 - 64 * b * c ^ 7 + 64 * b ^ 2 * c ^ 6
    - 512 * b ^ 3 * c ^ 5 + 928 * b ^ 4 * c ^ 4 + 192 * b ^ 5 * c ^ 3
    - 1088 * b ^ 6 * c ^ 2 + 384 * b ^ 7 * c + 80 * b ^ 8
    - 16 * c ^ 9 + 48 * b * c ^ 8 - 304 * b ^ 2 * c ^ 7
    - 368 * b ^ 3 * c ^ 6 + 656 * b ^ 4 * c ^ 5 + 592 * b ^ 5 * c ^ 4
    - 336 * b ^ 6 * c ^ 3 - 272 * b ^ 7 * c ^ 2 - 48 * b * c ^ 9
    - 272 * b ^ 2 * c ^ 8 - 352 * b ^ 3 * c ^ 7 + 96 * b ^ 4 * c ^ 6
    + 400 * b ^ 5 * c ^ 5 + 176 * b ^ 6 * c ^ 4 - 32 * b * c ^ 10
    - 128 * b ^ 2 * c ^ 9 - 192 * b ^ 3 * c ^ 8 - 128 * b ^ 4 * c ^ 7
    - 32 * b ^ 5 * c ^ 6

private def reverseCQuotient (b c : ℚ) : ℚ :=
  8 * c ^ 3 - 40 * b * c ^ 2 + 56 * b ^ 2 * c - 24 * b ^ 3
    - 4 * c ^ 4 - 20 * b * c ^ 3 + 4 * b ^ 2 * c ^ 2 + 20 * b ^ 3 * c
    - 8 * c ^ 5 - 16 * b * c ^ 4 - 8 * b ^ 2 * c ^ 3

private lemma reverse_b_poly (b c : ℚ) (hΦ : Phi10 b c = 0) :
    b * reverseUNum b c * reverseDNum b c ^ 2 =
      reverseUDen b c * (reverseUNum b c - reverseUDen b c) ^ 3 *
        (reverseUNum b c + reverseUDen b c) := by
  have hmul :
      b * reverseUNum b c * reverseDNum b c ^ 2 -
          reverseUDen b c * (reverseUNum b c - reverseUDen b c) ^ 3 *
            (reverseUNum b c + reverseUDen b c) =
        Phi10 b c * reverseBQuotient b c := by
    simp only [reverseUNum, reverseUDen, reverseDNum, reverseBQuotient, Phi10]
    ring_nf
  have hzero :
      b * reverseUNum b c * reverseDNum b c ^ 2 -
          reverseUDen b c * (reverseUNum b c - reverseUDen b c) ^ 3 *
            (reverseUNum b c + reverseUDen b c) = 0 := by
    simpa [hΦ] using hmul
  nlinarith

private lemma reverse_c_poly (b c : ℚ) (hΦ : Phi10 b c = 0) :
    c * reverseUNum b c * reverseDNum b c =
      reverseUDen b c * (reverseUNum b c - reverseUDen b c) *
        (reverseUNum b c + reverseUDen b c) := by
  have hmul :
      c * reverseUNum b c * reverseDNum b c -
          reverseUDen b c * (reverseUNum b c - reverseUDen b c) *
            (reverseUNum b c + reverseUDen b c) =
        Phi10 b c * reverseCQuotient b c := by
    simp only [reverseUNum, reverseUDen, reverseDNum, reverseCQuotient, Phi10]
    ring_nf
  have hzero :
      c * reverseUNum b c * reverseDNum b c -
          reverseUDen b c * (reverseUNum b c - reverseUDen b c) *
            (reverseUNum b c + reverseUDen b c) = 0 := by
    simpa [hΦ] using hmul
  nlinarith

private lemma b_eq_b10_uOfTateParameters
    (b c : ℚ) (hbc : b - c ≠ 0) (hΦ : Phi10 b c = 0)
    (hu : uOfTateParameters b c ≠ 0) :
    b = b10 (uOfTateParameters b c) := by
  set u := uOfTateParameters b c with hu_def
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := by
    simpa [hu_def] using u2_sub_4u_sub_1_ne_zero (uOfTateParameters b c)
  have hD' : u * (u - 4) - 1 ≠ 0 := by
    intro h
    apply hD
    ring_nf at h ⊢
    exact h
  have hpoly := reverse_b_poly b c hΦ
  unfold b10
  field_simp [hu, hD']
  rw [hu_def]
  unfold uOfTateParameters
  field_simp [hbc]
  simp only [reverseUNum, reverseUDen, reverseDNum] at hpoly
  ring_nf at hpoly ⊢
  exact hpoly

private lemma c_eq_c10_uOfTateParameters
    (b c : ℚ) (hbc : b - c ≠ 0) (hΦ : Phi10 b c = 0)
    (hu : uOfTateParameters b c ≠ 0) :
    c = c10 (uOfTateParameters b c) := by
  set u := uOfTateParameters b c with hu_def
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := by
    simpa [hu_def] using u2_sub_4u_sub_1_ne_zero (uOfTateParameters b c)
  have hD' : u * (u - 4) - 1 ≠ 0 := by
    intro h
    apply hD
    ring_nf at h ⊢
    exact h
  have hpoly := reverse_c_poly b c hΦ
  unfold c10
  field_simp [hu, hD']
  rw [hu_def]
  unfold uOfTateParameters
  field_simp [hbc]
  simp only [reverseUNum, reverseUDen, reverseDNum] at hpoly
  ring_nf at hpoly ⊢
  exact hpoly

lemma exists_u_of_Phi10 (b c : ℚ) (_hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b - c ≠ 0) (hΦ : Phi10 b c = 0) :
    ∃ u : ℚ, u ≠ 0 ∧ u ^ 2 - 4 * u - 1 ≠ 0 ∧ b = b10 u ∧ c = c10 u := by
  refine ⟨uOfTateParameters b c, ?_, ?_, ?_, ?_⟩
  · exact uOfTateParameters_ne_zero_of_Phi10 b c hc hbc hΦ
  · exact u2_sub_4u_sub_1_ne_zero (uOfTateParameters b c)
  · exact b_eq_b10_uOfTateParameters b c hbc hΦ
      (uOfTateParameters_ne_zero_of_Phi10 b c hc hbc hΦ)
  · exact c_eq_c10_uOfTateParameters b c hbc hΦ
      (uOfTateParameters_ne_zero_of_Phi10 b c hc hbc hΦ)

def tateX5 (b c : ℚ) : ℚ :=
  -b * c * (b - c ^ 2 - c) / (b - c) ^ 2

def tateY5 (b c : ℚ) : ℚ :=
  b * c ^ 2 * (b ^ 2 - b * c - c ^ 3) / (b - c) ^ 3

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

private def tateOriginPoint (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private lemma tate_point_nonsingular_of_equation
    (b c x y : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (h :
      y ^ 2 + (1 - c) * x * y - b * y =
        x ^ 3 - b * x ^ 2) :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) x y := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]
  nlinarith

private lemma tate_twoP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) :
    ∃ h2 : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) b (b * c),
      (2 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some b (b * c) h2 := by
  let W := tateNormalFormCurve b c
  have h2 : WeierstrassCurve.Affine.Nonsingular W b (b * c) := by
    apply tate_point_nonsingular_of_equation
    ring
  refine ⟨h2, ?_⟩
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    simpa [W, tateNormalFormCurve, WeierstrassCurve.Affine.negY, eq_comm] using hb
  rw [two_nsmul]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY]
  · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp [W, tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    ring

private lemma tate_threeP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) :
    ∃ h3 : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) c (b - c),
      (3 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some c (b - c) h3 := by
  let W := tateNormalFormCurve b c
  rcases tate_twoP_eq b c hb with ⟨h2, h2eq⟩
  have h3 : WeierstrassCurve.Affine.Nonsingular W c (b - c) := by
    apply tate_point_nonsingular_of_equation
    ring
  refine ⟨h3, ?_⟩
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    field_simp [hb]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    field_simp [hb]
    ring

private lemma tate_fourP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ h4 : WeierstrassCurve.Affine.Nonsingular
        (tateNormalFormCurve b c)
        (b * (b - c) / c ^ 2)
        (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3),
      (4 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3) h4 := by
  let W := tateNormalFormCurve b c
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  have h4 : WeierstrassCurve.Affine.Nonsingular W
      (b * (b - c) / c ^ 2)
      (-b ^ 2 * (b - c ^ 2 - c) / c ^ 3) := by
    apply tate_point_nonsingular_of_equation
    field_simp [hc]
    ring
  refine ⟨h4, ?_⟩
  rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h3eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    field_simp [hc]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring

private lemma tate_fiveP_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b - c ≠ 0) :
    ∃ h5 : WeierstrassCurve.Affine.Nonsingular
        (tateNormalFormCurve b c) (tateX5 b c) (tateY5 b c),
      (5 : ℕ) • tateOriginPoint b c =
        WeierstrassCurve.Affine.Point.some (tateX5 b c) (tateY5 b c) h5 := by
  let W := tateNormalFormCurve b c
  rcases tate_fourP_eq b c hb hc with ⟨h4, h4eq⟩
  have h5 : WeierstrassCurve.Affine.Nonsingular W (tateX5 b c) (tateY5 b c) := by
    apply tate_point_nonsingular_of_equation
    unfold tateX5 tateY5
    field_simp [hbc]
    ring
  refine ⟨h5, ?_⟩
  have hx4 : b * (b - c) / c ^ 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hb hbc) (pow_ne_zero 2 hc)
  rw [show (5 : ℕ) = 4 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h4eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx4]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx4]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX]
    unfold tateX5
    field_simp [hb, hc, hbc]
    ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hx4]
    simp [tateNormalFormCurve, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY]
    unfold tateY5
    field_simp [hb, hc, hbc]
    ring

private lemma tate_fourP_eq_zero_of_c_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hc0 : c = 0) :
    (4 : ℕ) • tateOriginPoint b c = 0 := by
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h3eq]
  simp only [tateOriginPoint]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hc0]
  simp [tateNormalFormCurve, WeierstrassCurve.Affine.negY, hc0]

private lemma tate_fiveP_eq_zero_of_b_eq_c
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)]
    (hb : b ≠ 0) (hbc_eq : b = c) :
    (5 : ℕ) • tateOriginPoint b c = 0 := by
  rcases tate_twoP_eq b c hb with ⟨h2, h2eq⟩
  rcases tate_threeP_eq b c hb with ⟨h3, h3eq⟩
  rw [show (5 : ℕ) = 2 + 3 by norm_num, add_nsmul]
  rw [h2eq, h3eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hbc_eq]
  rw [WeierstrassCurve.Affine.negY]
  simp [tateNormalFormCurve, hbc_eq]
  ring

private lemma origin_three_nsmul_eq_zero_of_a2_eq_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {h0 : WeierstrassCurve.Affine.Nonsingular W 0 0}
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ ≠ 0)
    (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h0 :
          WeierstrassCurve.Affine.Point W) = 0 := by
  let O : WeierstrassCurve.Affine.Point W :=
    WeierstrassCurve.Affine.Point.some 0 0 h0
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    intro h
    apply ha₃
    rw [WeierstrassCurve.Affine.negY] at h
    linarith
  have h2 : WeierstrassCurve.Affine.Nonsingular W 0 (-W.a₃) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [ha₂, ha₄, ha₆]
    ring
  have h2eq :
      (2 : ℕ) • O =
        WeierstrassCurve.Affine.Point.some 0 (-W.a₃) h2 := by
    rw [two_nsmul]
    simp only [O]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

lemma Phi10_of_tate_5P_twoTorsion (b c : ℚ) (hb : b ≠ 0) (hbc : b - c ≠ 0)
    (h5P2 : 2 * tateY5 b c + (1 - c) * tateX5 b c - b = 0) :
    Phi10 b c = 0 := by
  unfold tateX5 tateY5 at h5P2
  field_simp [hb, hbc] at h5P2
  ring_nf at h5P2
  have hprod : b * Phi10 b c = 0 := by
    unfold Phi10
    ring_nf
    linear_combination -h5P2
  exact (mul_eq_zero.mp hprod).resolve_left hb

private lemma tateTwoTorsionCubic_factor_aux
    (u D B C A X : ℚ) (hu : u ≠ 0) (hD : D ≠ 0)
    (hC : C = (u - 1) * (u + 1))
    (hB : B = (u - 1) ^ 3 * (u + 1))
    (hA : A = u ^ 3 - 3 * u ^ 2 - u + 1)
    (hDdef : D = u ^ 2 - 4 * u - 1) :
    tateTwoTorsionCubic (B / (u * D ^ 2)) (C / (u * D)) X =
      (X - (-(B / (4 * u ^ 2 * D)))) *
        (4 * X ^ 2 - (8 * A / D ^ 2) * X + 4 * B / D ^ 3) := by
  subst C
  subst B
  subst A
  unfold tateTwoTorsionCubic
  field_simp [hu, hD]
  subst D
  ring_nf

lemma tateTwoTorsionCubic_b10_c10_factor (u X : ℚ) (hu : u ≠ 0)
    (hD : u ^ 2 - 4 * u - 1 ≠ 0) :
    tateTwoTorsionCubic (b10 u) (c10 u) X = (X - x5_10 u) * Q10 u X := by
  unfold b10 c10 x5_10 Q10
  have h := tateTwoTorsionCubic_factor_aux u (u ^ 2 - 4 * u - 1)
    ((u - 1) ^ 3 * (u + 1)) ((u - 1) * (u + 1))
    (u ^ 3 - 3 * u ^ 2 - u + 1) X hu hD rfl rfl rfl rfl
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

lemma Q10_root_of_indep_2torsion (u xT : ℚ) (hu : u ≠ 0)
    (hT2 : tateTwoTorsionCubic (b10 u) (c10 u) xT = 0)
    (hne : xT ≠ x5_10 u) :
    Q10 u xT = 0 := by
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := u2_sub_4u_sub_1_ne_zero u
  have hfactor := tateTwoTorsionCubic_b10_c10_factor u xT hu hD
  rw [hfactor] at hT2
  exact (mul_eq_zero.mp hT2).resolve_left (sub_ne_zero.mpr hne)

/--
Pure group-theory extraction from an injective `ZMod 2 × ZMod 10`.

Lean's additive order is `addOrderOf`; this is the additive version of the
roadmap's `orderOf P = 10`.
-/
theorem injective_Z2xZ10_gives_order10_and_independent_2torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point) (hf : Function.Injective f) :
    let P := f ((0 : ZMod 2), (1 : ZMod 10))
    let T := f ((1 : ZMod 2), (0 : ZMod 10))
    addOrderOf P = 10 ∧
      (2 : ℕ) • T = 0 ∧ T ≠ 0 ∧
      (5 : ℕ) • P = f ((0 : ZMod 2), (5 : ZMod 10)) ∧
      (5 : ℕ) • P ≠ 0 ∧
      (2 : ℕ) • ((5 : ℕ) • P) = 0 ∧
      T ≠ (5 : ℕ) • P := by
  classical
  let p0 : ZMod 2 × ZMod 10 := ((0 : ZMod 2), (1 : ZMod 10))
  let t0 : ZMod 2 × ZMod 10 := ((1 : ZMod 2), (0 : ZMod 10))
  let p5 : ZMod 2 × ZMod 10 := ((0 : ZMod 2), (5 : ZMod 10))
  have hp0_order : addOrderOf p0 = 10 := by
    simp [p0, Prod.addOrderOf_mk]
  have hP_order : addOrderOf (f p0) = 10 := by
    rw [addOrderOf_injective f hf, hp0_order]
  have ht0_two : (2 : ℕ) • t0 = 0 := by
    decide
  have hT_two : (2 : ℕ) • f t0 = 0 := by
    rw [← f.map_nsmul, ht0_two, map_zero]
  have ht0_ne_zero : t0 ≠ 0 := by
    decide
  have hT_ne_zero : f t0 ≠ 0 := by
    intro h
    exact ht0_ne_zero (hf (by simpa using h))
  have hp5_eq : (5 : ℕ) • p0 = p5 := by
    decide
  have h5P_eq : (5 : ℕ) • f p0 = f p5 := by
    rw [← f.map_nsmul, hp5_eq]
  have hp5_ne_zero : p5 ≠ 0 := by
    decide
  have h5P_ne_zero : (5 : ℕ) • f p0 ≠ 0 := by
    intro h
    rw [h5P_eq] at h
    exact hp5_ne_zero (hf (by simpa using h))
  have hp5_two : (2 : ℕ) • p5 = 0 := by
    decide
  have h5P_two : (2 : ℕ) • ((5 : ℕ) • f p0) = 0 := by
    rw [h5P_eq, ← f.map_nsmul, hp5_two, map_zero]
  have ht0_ne_p5 : t0 ≠ p5 := by
    decide
  have hT_ne_5P : f t0 ≠ (5 : ℕ) • f p0 := by
    intro h
    rw [h5P_eq] at h
    exact ht0_ne_p5 (hf h)
  simpa [p0, t0, p5] using
    And.intro hP_order <|
      And.intro hT_two <|
      And.intro hT_ne_zero <|
      And.intro h5P_eq <|
      And.intro h5P_ne_zero <|
      And.intro h5P_two hT_ne_5P

/--
The transformed `X`-coordinate under a Weierstrass variable change.  This is
the inverse coordinate map from old coordinates on `W` to new coordinates on
`C • W`.
-/
def variableChangePointX (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) : ℚ :=
  (C.u⁻¹ : ℚ) ^ 2 * (x - C.r)

/-- The transformed `Y`-coordinate under a Weierstrass variable change. -/
def variableChangePointY (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) : ℚ :=
  (C.u⁻¹ : ℚ) ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The old `x`-coordinate recovered from new coordinates. -/
def variableChangePointInvX (C : WeierstrassCurve.VariableChange ℚ) (X : ℚ) : ℚ :=
  (C.u : ℚ) ^ 2 * X + C.r

/-- The old `y`-coordinate recovered from new coordinates. -/
def variableChangePointInvY (C : WeierstrassCurve.VariableChange ℚ) (X Y : ℚ) : ℚ :=
  (C.u : ℚ) ^ 3 * Y + (C.u : ℚ) ^ 2 * C.s * X + C.t

lemma variableChangePoint_equation
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) {x y : ℚ}
    (h : WeierstrassCurve.Affine.Equation W x y) :
    WeierstrassCurve.Affine.Equation (C • W)
      (variableChangePointX C x) (variableChangePointY C x y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointX variableChangePointY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  linear_combination h

lemma variableChangePointInv_equation
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) {X Y : ℚ}
    (h : WeierstrassCurve.Affine.Equation (C • W) X Y) :
    WeierstrassCurve.Affine.Equation W
      (variableChangePointInvX C X) (variableChangePointInvY C X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointInvX variableChangePointInvY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆] at h
  simp only [Units.val_inv_eq_inv_val] at h
  field_simp [C.u.ne_zero] at h
  linear_combination h

lemma variableChangePointInvX_pointX
    (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) :
    variableChangePointInvX C (variableChangePointX C x) = x := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointInvY_pointY
    (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    variableChangePointInvY C (variableChangePointX C x) (variableChangePointY C x y) = y := by
  simp [variableChangePointInvY, variableChangePointX, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_invX
    (C : WeierstrassCurve.VariableChange ℚ) (X : ℚ) :
    variableChangePointX C (variableChangePointInvX C X) = X := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointY_invY
    (C : WeierstrassCurve.VariableChange ℚ) (X Y : ℚ) :
    variableChangePointY C (variableChangePointInvX C X)
      (variableChangePointInvY C X Y) = Y := by
  simp [variableChangePointInvX, variableChangePointInvY, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_eq_iff
    (C : WeierstrassCurve.VariableChange ℚ) {x₁ x₂ : ℚ} :
    variableChangePointX C x₁ = variableChangePointX C x₂ ↔ x₁ = x₂ := by
  unfold variableChangePointX
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linarith
  · intro h
    simp [h]

lemma variableChangePointY_eq_iff
    (C : WeierstrassCurve.VariableChange ℚ) (x : ℚ) {y₁ y₂ : ℚ} :
    variableChangePointY C x y₁ = variableChangePointY C x y₂ ↔ y₁ = y₂ := by
  unfold variableChangePointY
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linarith
  · intro h
    simp [h]

lemma variableChangePointY_negY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ) (x y : ℚ) :
    variableChangePointY C x (WeierstrassCurve.Affine.negY W x y) =
      WeierstrassCurve.Affine.negY (C • W)
        (variableChangePointX C x) (variableChangePointY C x y) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_slope_of_X_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

lemma variableChange_slope_of_Y_ne
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  have hy_eq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
  have hy_self : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
    intro h
    apply hy
    rw [← hx, ← hy_eq]
    exact h
  have hden : x₁ * W.a₁ + W.a₃ + y₁ * 2 ≠ 0 := by
    intro hden
    apply hy_self
    rw [WeierstrassCurve.Affine.negY]
    linarith
  have hmul :
      (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htarget_hx :
      variableChangePointX C x₁ = variableChangePointX C x₂ := by
    simp [hx]
  have htarget_hy :
      variableChangePointY C x₁ y₁ ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x₁).mp
    rw [h]
    rw [hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htarget_hx htarget_hy]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

lemma variableChange_slope
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · exact variableChange_slope_of_Y_ne W C h₁ h₂ hx (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne W C hx

lemma variableChange_nonvertical
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    ¬(variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂)) := by
  rintro ⟨hx', hy'⟩
  apply hxy
  have hx : x₁ = x₂ := (variableChangePointX_eq_iff C).mp hx'
  refine ⟨hx, ?_⟩
  rw [← hx]
  apply (variableChangePointY_eq_iff C x₁).mp
  rw [hy', hx, ← variableChangePointY_negY]

lemma variableChange_vertical
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x₁ x₂ y₁ y₂ : ℚ}
    (hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂) :
    variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
  rcases hxy with ⟨hx, hy⟩
  constructor
  · simp [hx]
  · rw [hy, ← variableChangePointY_negY, hx]

lemma variableChange_addX
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ ℓ : ℚ) :
    variableChangePointX C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ) =
      WeierstrassCurve.Affine.addX (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        ((C.u⁻¹ : ℚ) * (ℓ - C.s)) := by
  simp [variableChangePointX, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_addY
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (x₁ x₂ y₁ ℓ : ℚ) :
    variableChangePointY C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ)
        (WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ) =
      WeierstrassCurve.Affine.addY (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) ((C.u⁻¹ : ℚ) * (ℓ - C.s)) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

noncomputable def variableChangePointMap
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W → WeierstrassCurve.Affine.Point (C • W)
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX C x) (variableChangePointY C x y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePoint_equation W C h.left))

noncomputable def variableChangePointMapInv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point (C • W) → WeierstrassCurve.Affine.Point W
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some X Y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointInvX C X) (variableChangePointInvY C X Y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePointInv_equation W C h.left))

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    variableChangePointMap W C 0 = 0 :=
  rfl

lemma variableChangePointMap_leftInverse
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    Function.LeftInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointInvX_pointX, variableChangePointInvY_pointY]

lemma variableChangePointMap_rightInverse
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    Function.RightInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some X Y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointX_invX, variableChangePointY_invY]

noncomputable def variableChangePointEquiv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W ≃ WeierstrassCurve.Affine.Point (C • W) where
  toFun := variableChangePointMap W C
  invFun := variableChangePointMapInv W C
  left_inv := variableChangePointMap_leftInverse W C
  right_inv := variableChangePointMap_rightInverse W C

lemma variableChangePointMap_neg
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    (P : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (-P) = -variableChangePointMap W C P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [variableChangePointMap, WeierstrassCurve.Affine.Point.neg_some]
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, variableChangePointY_negY W C x y⟩

lemma variableChangePointMap_add
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (P + Q) =
      variableChangePointMap W C P + variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope W C h₁.left h₂.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · change
            variableChangePointX C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addX W C x₁ x₂
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)
        · change
            variableChangePointY C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂))
                (WeierstrassCurve.Affine.addY W x₁ x₂ y₁
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (variableChangePointY C x₁ y₁)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addY W C x₁ x₂ y₁
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)

noncomputable def variableChangePointAddEquiv
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ) :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point (C • W) :=
  AddEquiv.mk (variableChangePointEquiv W C) (variableChangePointMap_add W C)

private noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private lemma pointCurveEqAddEquiv_some
    {W W' : WeierstrassCurve ℚ} (h : W = W') {x y : ℚ}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    pointCurveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst h
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/--
The remaining explicit geometric computation.

Starting from an order-10 point and an independent rational 2-torsion point,
one must normalize the curve to Tate form with the order-10 point at `(0,0)`,
prove the non-degeneracy conditions `b ≠ 0`, `c ≠ 0`, `b - c ≠ 0`, compute the
coordinate of `5P` as `(tateX5 b c, tateY5 b c)`, and transport the independent
2-torsion point to a distinct affine 2-torsion point `(xT,yT)`.

All downstream algebra from these normalized coordinate facts is proved below.
The unproved part is now just this bounded group-law/normalization calculation,
not the final extraction of the Tate two-torsion cubic root.
-/
theorem exists_tate_normalized_order10_coordinate_data
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point)
    (hP : addOrderOf P = 10)
    (hT2 : (2 : ℕ) • T = 0)
    (hTne0 : T ≠ 0)
    (h5Pne0 : (5 : ℕ) • P ≠ 0)
    (h5P2 : (2 : ℕ) • ((5 : ℕ) • P) = 0)
    (hTne5P : T ≠ (5 : ℕ) • P) :
    ∃ b c xT yT : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
      ∃ hT : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) xT yT,
      ∃ h5 : WeierstrassCurve.Affine.Nonsingular
          (tateNormalFormCurve b c) (tateX5 b c) (tateY5 b c),
        b ≠ 0 ∧ c ≠ 0 ∧ b - c ≠ 0 ∧
          (2 : ℕ) •
              (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0 ∧
          (2 : ℕ) •
              (WeierstrassCurve.Affine.Point.some (tateX5 b c) (tateY5 b c) h5 :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0 ∧
          (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) ≠
            WeierstrassCurve.Affine.Point.some (tateX5 b c) (tateY5 b c) h5 := by
  let Psmall :
      ∀ m < 10, 0 < m → (m : ℕ) • P ≠ 0 :=
    ((addOrderOf_eq_iff (x := P) (by norm_num : 0 < 10)).mp hP).2
  cases P with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hP
      norm_num at hP
  | some x₀ y₀ hPaff =>
      let hPaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        change WeierstrassCurve.Affine.Nonsingular (E⁄ℚ) x₀ y₀
        exact hPaff
      let P₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hPaffE
      have hP₀_order : addOrderOf P₀ = 10 := by
        dsimp [P₀, hPaffE]
        change addOrderOf (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff) = 10
        exact hP
      let Psmall₀ :
          ∀ m < 10, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by norm_num : 0 < 10)).mp hP₀_order).2
      have h5P2₀ : (2 : ℕ) • ((5 : ℕ) • P₀) = 0 := by
        dsimp [P₀, hPaffE]
        change (2 : ℕ) • ((5 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff : (E⁄ℚ).Point)) = 0
        exact h5P2
      have hTne5P₀ : T ≠ (5 : ℕ) • P₀ := by
        intro h
        apply hTne5P
        dsimp [P₀, hPaffE] at h
        exact h
      let T₀ : WeierstrassCurve.Affine.Point E := T
      have hT2₀ : (2 : ℕ) • T₀ = 0 := by
        change (2 : ℕ) • (T : WeierstrassCurve.Affine.Point E) = 0
        simpa using hT2
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden0
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h2zero : (2 : ℕ) • P₀ = 0 := by
          simpa [P₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hPaff) hy)
        exact Psmall₀ 2 (by norm_num) (by norm_num) h2zero
      let C0 := translateToOriginTangent E x₀ y₀
      let W1 : WeierstrassCurve ℚ := C0 • E
      haveI : W1.IsElliptic := by
        dsimp [W1]
        infer_instance
      let φ0 : WeierstrassCurve.Affine.Point E ≃+
          WeierstrassCurve.Affine.Point W1 := by
        dsimp [W1]
        exact variableChangePointAddEquiv E C0
      have hW1a₆ : W1.a₆ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₆_eq_zero E (x₀ := x₀) (y₀ := y₀) hPaffE.1
      have hW1a₄ : W1.a₄ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₄_eq_zero E (x₀ := x₀) (y₀ := y₀) hden
      have hW1a₃_formula : W1.a₃ = E.a₃ + E.a₁ * x₀ + 2 * y₀ := by
        simp [W1, C0]
      have hW1a₃_ne : W1.a₃ ≠ 0 := by
        rw [hW1a₃_formula]
        intro h
        apply hden
        linarith
      have hW1origin : WeierstrassCurve.Affine.Nonsingular W1 0 0 := by
        apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        rw [WeierstrassCurve.Affine.equation_iff]
        simp [hW1a₆]
      have hφ0P_origin :
          φ0 P₀ = WeierstrassCurve.Affine.Point.some 0 0 hW1origin := by
        change variableChangePointMap E C0 P₀ =
          WeierstrassCurve.Affine.Point.some 0 0 hW1origin
        dsimp [variableChangePointMap, P₀]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor <;>
          simp [C0, variableChangePointX,
            variableChangePointY, translateToOriginTangent]
      have hW1a₂_ne : W1.a₂ ≠ 0 := by
        intro hW1a₂
        have h3zero_origin :
            (3 : ℕ) •
                (WeierstrassCurve.Affine.Point.some 0 0 hW1origin :
                  WeierstrassCurve.Affine.Point W1) = 0 :=
          origin_three_nsmul_eq_zero_of_a2_eq_zero W1 hW1a₂ hW1a₃_ne hW1a₄ hW1a₆
        have h3zero_map : (3 : ℕ) • φ0 P₀ = 0 := by
          simpa [hφ0P_origin] using h3zero_origin
        have h3zero : (3 : ℕ) • P₀ = 0 := by
          apply (EquivLike.injective φ0)
          rw [map_nsmul, h3zero_map, map_zero]
        exact Psmall₀ 3 (by norm_num) (by norm_num) h3zero
      let ρ : ℚ := W1.a₃ / W1.a₂
      have hρ : ρ ≠ 0 := div_ne_zero hW1a₃_ne hW1a₂_ne
      let C1 := scaleByRho ρ hρ
      let b : ℚ := tateBFromCoefficients W1.a₂ W1.a₃
      let c : ℚ := tateCFromCoefficients W1.a₁ W1.a₂ W1.a₃
      have hW2eq : C1 • W1 = tateNormalFormCurve b c := by
        ext <;> dsimp [C1, ρ, b, c, tateNormalFormCurve,
          tateBFromCoefficients, tateCFromCoefficients]
        · rw [WeierstrassCurve.variableChange_a₁]
          simp [scaleByRho]
          field_simp [hW1a₂_ne, hW1a₃_ne]
        · rw [scaleByTateRho_a₂ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · rw [scaleByTateRho_a₃ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · simp [WeierstrassCurve.variableChange_a₄, scaleByRho, hW1a₄]
        · simp [WeierstrassCurve.variableChange_a₆, scaleByRho, hW1a₆]
      haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := by
        rw [← hW2eq]
        infer_instance
      let φ1raw : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (C1 • W1) :=
        variableChangePointAddEquiv W1 C1
      let φ1 : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
        φ1raw.trans (pointCurveEqAddEquiv hW2eq)
      have hφ1φ0P_origin :
          φ1 (φ0 P₀) = tateOriginPoint b c := by
        rw [hφ0P_origin]
        have hRawOrigin : WeierstrassCurve.Affine.Nonsingular (C1 • W1) 0 0 := by
          simpa [hW2eq] using tate_origin_nonsingular b c
        have hφ1raw_origin :
            φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
              WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin := by
          change variableChangePointMap W1 C1
              (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
            WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin
          dsimp [variableChangePointMap]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor <;>
            simp [C1, variableChangePointX, variableChangePointY,
              scaleByRho]
        change (pointCurveEqAddEquiv hW2eq)
            (φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin)) =
          tateOriginPoint b c
        rw [hφ1raw_origin]
        exact pointCurveEqAddEquiv_some hW2eq
      have hOriginOrder : addOrderOf (tateOriginPoint b c) = 10 := by
        have hmaporder : addOrderOf (φ1 (φ0 P₀)) = 10 := by
          calc
            addOrderOf (φ1 (φ0 P₀)) = addOrderOf (φ0 P₀) :=
              addOrderOf_injective φ1.toAddMonoidHom (EquivLike.injective φ1) (φ0 P₀)
            _ = addOrderOf P₀ :=
              addOrderOf_injective φ0.toAddMonoidHom (EquivLike.injective φ0) P₀
            _ = 10 := hP₀_order
        rw [hφ1φ0P_origin] at hmaporder
        exact hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W1.a₂ ^ 3 / W1.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW1a₂_ne) (pow_ne_zero 2 hW1a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      have hOriginSmall :
          ∀ m < 10, 0 < m → (m : ℕ) • tateOriginPoint b c ≠ 0 :=
        ((addOrderOf_eq_iff (x := tateOriginPoint b c) (by norm_num : 0 < 10)).mp
          hOriginOrder).2
      have hc : c ≠ 0 := by
        intro hc0
        exact hOriginSmall 4 (by norm_num) (by norm_num)
          (tate_fourP_eq_zero_of_c_eq_zero b c hb hc0)
      have hbc : b - c ≠ 0 := by
        intro hbc0
        exact hOriginSmall 5 (by norm_num) (by norm_num)
          (tate_fiveP_eq_zero_of_b_eq_c b c hb (sub_eq_zero.mp hbc0))
      rcases tate_fiveP_eq b c hb hc hbc with ⟨h5, h5eq⟩
      have hT2map : (2 : ℕ) • φ1 (φ0 T₀) = 0 := by
        calc
          (2 : ℕ) • φ1 (φ0 T₀) = φ1 ((2 : ℕ) • φ0 T₀) :=
            (map_nsmul φ1 2 (φ0 T₀)).symm
          _ = φ1 (φ0 ((2 : ℕ) • T₀)) := by
            rw [← map_nsmul φ0 2 T₀]
          _ = 0 := by
            rw [hT2₀, map_zero, map_zero]
      have h5two_origin : (2 : ℕ) • ((5 : ℕ) • tateOriginPoint b c) = 0 := by
        rw [← hφ1φ0P_origin]
        rw [← map_nsmul φ1 5 (φ0 P₀)]
        rw [← map_nsmul φ1 2 ((5 : ℕ) • φ0 P₀)]
        rw [← map_nsmul φ0 5 P₀]
        rw [← map_nsmul φ0 2 ((5 : ℕ) • P₀)]
        rw [h5P2₀, map_zero, map_zero]
      have hTmap_ne0 : φ1 (φ0 T₀) ≠ 0 := by
        intro hT0
        have hφ0T0 : φ0 T₀ = 0 := by
          apply (EquivLike.injective φ1)
          simpa [map_zero] using hT0
        have hT₀0 : T₀ = 0 := by
          apply (EquivLike.injective φ0)
          simpa [map_zero] using hφ0T0
        apply hTne0
        exact hT₀0
      have hTmap_ne5 : φ1 (φ0 T₀) ≠ (5 : ℕ) • tateOriginPoint b c := by
        intro hT5
        apply hTne5P₀
        change T₀ = (5 : ℕ) • P₀
        apply (EquivLike.injective φ0)
        apply (EquivLike.injective φ1)
        rw [map_nsmul φ0, map_nsmul φ1, hφ1φ0P_origin]
        exact hT5
      cases hTpoint : φ1 (φ0 T₀) with
      | zero =>
          exact False.elim (hTmap_ne0 hTpoint)
      | some xT yT hT =>
          refine ⟨b, c, xT, yT, inferInstance, hT, h5, hb, hc, hbc, ?_, ?_, ?_⟩
          · simpa [hTpoint] using hT2map
          · rw [← h5eq]
            exact h5two_origin
          · intro hsame
            apply hTmap_ne5
            rw [hTpoint, h5eq]
            exact hsame

/--
The remaining normalization bridge for the `ZMod 2 × ZMod 10` reduction.

This is the single geometric glue statement: after moving an order-10 point to
Tate normal form, the independent rational 2-torsion point supplies a distinct
root of the Tate two-torsion cubic.
-/
theorem exists_tate_parameters_of_order10_and_independent_2torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point)
    (hP : addOrderOf P = 10)
    (hT2 : (2 : ℕ) • T = 0)
    (hTne0 : T ≠ 0)
    (h5Pne0 : (5 : ℕ) • P ≠ 0)
    (h5P2 : (2 : ℕ) • ((5 : ℕ) • P) = 0)
    (hTne5P : T ≠ (5 : ℕ) • P) :
    ∃ b c xT : ℚ,
      b ≠ 0 ∧ c ≠ 0 ∧ b - c ≠ 0 ∧
        2 * tateY5 b c + (1 - c) * tateX5 b c - b = 0 ∧
        tateTwoTorsionCubic b c xT = 0 ∧ xT ≠ tateX5 b c := by
  rcases exists_tate_normalized_order10_coordinate_data
      E P T hP hT2 hTne0 h5Pne0 h5P2 hTne5P with
    ⟨b, c, xT, yT, hEll, hT, h5, hb, hc, hbc, hT2', h5P2', hne⟩
  haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := hEll
  refine ⟨b, c, xT, hb, hc, hbc, ?_, ?_, ?_⟩
  · exact tate_linear_relation_of_two_torsion
      (b := b) (c := c) (x := tateX5 b c) (y := tateY5 b c) (h := h5) h5P2'
  · exact tate_cubic_of_two_torsion
      (b := b) (c := c) (x := xT) (y := yT) (h := hT) hT2'
  · exact tate_two_torsion_x_ne_of_point_ne
      (b := b) (c := c) (x₁ := xT) (y₁ := yT)
      (x₂ := tateX5 b c) (y₂ := tateY5 b c)
      (h₁ := hT) (h₂ := h5) hT2' h5P2' hne

lemma b10_sub_c10 (u : ℚ) (hu : u ≠ 0) :
    b10 u - c10 u =
      (2 * (u - 1) * (u + 1) ^ 2) / (u * (u ^ 2 - 4 * u - 1) ^ 2) := by
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := u2_sub_4u_sub_1_ne_zero u
  unfold b10 c10
  field_simp [hu, hD]
  ring

lemma b10_sub_c10_sq_sub_c10 (u : ℚ) (hu : u ≠ 0) :
    b10 u - (c10 u) ^ 2 - c10 u =
      ((u - 1) * (u + 1) ^ 3) / (u ^ 2 * (u ^ 2 - 4 * u - 1) ^ 2) := by
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := u2_sub_4u_sub_1_ne_zero u
  unfold b10 c10
  field_simp [hu, hD]
  ring

lemma tateX5_b10_c10_eq_x5_10
    (u : ℚ) (hu : u ≠ 0) (hu1 : u ≠ 1) (hum1 : u ≠ -1) :
    tateX5 (b10 u) (c10 u) = x5_10 u := by
  have hD : u ^ 2 - 4 * u - 1 ≠ 0 := u2_sub_4u_sub_1_ne_zero u
  have hsub : u - 1 ≠ 0 := by
    intro h
    apply hu1
    linarith
  have hadd : u + 1 ≠ 0 := by
    intro h
    apply hum1
    linarith
  unfold tateX5 x5_10
  rw [b10_sub_c10 u hu, b10_sub_c10_sq_sub_c10 u hu]
  unfold b10 c10
  field_simp [hu, hD, hsub, hadd]
  ring

theorem Z2xZ10_gives_non_degenerate_E20_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, (w ^ 2 = u ^ 3 + u ^ 2 - u) ∧ ¬(u = -1 ∨ u = 0 ∨ u = 1) := by
  rcases hE with ⟨f, hf⟩
  let P : (E⁄ℚ).Point := f ((0 : ZMod 2), (1 : ZMod 10))
  let T : (E⁄ℚ).Point := f ((1 : ZMod 2), (0 : ZMod 10))
  have hdata :=
    injective_Z2xZ10_gives_order10_and_independent_2torsion E f hf
  dsimp only [P, T] at hdata
  rcases hdata with
    ⟨hPorder, hT2, hTne0, _h5Peq, h5Pne0, h5P2, hTne5P⟩
  rcases exists_tate_parameters_of_order10_and_independent_2torsion
      E P T hPorder hT2 hTne0 h5Pne0 h5P2 hTne5P with
    ⟨b, c, xT, hb, hc, hbc, h5Ptwo, hTroot, hTne5⟩
  have hΦ : Phi10 b c = 0 :=
    Phi10_of_tate_5P_twoTorsion b c hb hbc h5Ptwo
  rcases exists_u_of_Phi10 b c hb hc hbc hΦ with
    ⟨u, hu, hD, hb_eq, hc_eq⟩
  have hu_ne_one : u ≠ 1 := by
    intro h
    apply hb
    rw [hb_eq, h]
    norm_num [b10]
  have hu_ne_neg_one : u ≠ -1 := by
    intro h
    apply hb
    rw [hb_eq, h]
    norm_num [b10]
  have hTroot_u : tateTwoTorsionCubic (b10 u) (c10 u) xT = 0 := by
    rw [← hb_eq, ← hc_eq]
    exact hTroot
  have hTne_x5 : xT ≠ x5_10 u := by
    intro hx
    apply hTne5
    rw [hx, hb_eq, hc_eq, tateX5_b10_c10_eq_x5_10 u hu hu_ne_one hu_ne_neg_one]
  have hQ : Q10 u xT = 0 :=
    Q10_root_of_indep_2torsion u xT hu hTroot_u hTne_x5
  exact ⟨u, w10 u xT, E20_point_of_Q10_root u xT hu hD hQ, by
    rintro (hu_neg | hu_zero | hu_one)
    · exact hu_ne_neg_one hu_neg
    · exact hu hu_zero
    · exact hu_ne_one hu_one⟩

end

end Scratch.TateZ2xZ10Reduction

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TateNormalFormBridge.lean (whole module, imports dropped). -/
section

/-!
# A reusable Tate-normal-form bridge

The N=10 and N=12 reductions contain the same normalization argument.  This
file extracts the part that depends only on a marked point of order greater
than three: after two explicit Weierstrass variable changes, the marked point
is `(0,0)` on Tate normal form and its additive order is preserved.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateNormalFormBridge

open Scratch.TateZ2xZ10Reduction

noncomputable section

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

/-- The marked origin on Tate normal form. -/
def tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private lemma pointCurveEqAddEquiv_some
    {W W' : WeierstrassCurve ℚ} (h : W = W') {x y : ℚ}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    pointCurveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst h
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-- On a Weierstrass equation with `a₂=a₄=a₆=0` and `a₃≠0`, the affine
origin is a flex and hence is killed by three.  This is the algebraic
degeneracy test used by Tate normalization when the translated quadratic
coefficient vanishes. -/
theorem origin_three_nsmul_eq_zero_of_a2_eq_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {h0 : WeierstrassCurve.Affine.Nonsingular W 0 0}
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ ≠ 0)
    (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h0 :
          WeierstrassCurve.Affine.Point W) = 0 := by
  let O : WeierstrassCurve.Affine.Point W :=
    WeierstrassCurve.Affine.Point.some 0 0 h0
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    intro h
    apply ha₃
    rw [WeierstrassCurve.Affine.negY] at h
    linarith
  have h2 : WeierstrassCurve.Affine.Nonsingular W 0 (-W.a₃) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [ha₂, ha₄, ha₆]
    ring
  have h2eq :
      (2 : ℕ) • O =
        WeierstrassCurve.Affine.Point.some 0 (-W.a₃) h2 := by
    rw [two_nsmul]
    simp only [O]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

/--
Any rational point of additive order `n > 3` can be moved to the marked
origin of a nonsingular Tate normal form.  The output parameter `b` is
nonzero; this is the only nondegeneracy factor needed for prime order 11.
-/
theorem exists_tate_normalized_of_addOrder_gt_three_with_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          (tateNormalFormCurve b c).j = E.j := by
  cases P with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hP
      omega
  | some x₀ y₀ hPaff =>
      let hPaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        change WeierstrassCurve.Affine.Nonsingular (E⁄ℚ) x₀ y₀
        exact hPaff
      let P₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hPaffE
      have hP₀_order : addOrderOf P₀ = n := by
        dsimp [P₀, hPaffE]
        change addOrderOf
          (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff) = n
        exact hP
      let Psmall₀ :
          ∀ m < n, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by omega)).mp hP₀_order).2
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden0
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h2zero : (2 : ℕ) • P₀ = 0 := by
          simpa [P₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hPaff) hy)
        exact Psmall₀ 2 (by omega) (by norm_num) h2zero
      let C0 := translateToOriginTangent E x₀ y₀
      let W1 : WeierstrassCurve ℚ := C0 • E
      haveI : W1.IsElliptic := by
        dsimp [W1]
        infer_instance
      let φ0 : WeierstrassCurve.Affine.Point E ≃+
          WeierstrassCurve.Affine.Point W1 := by
        dsimp [W1]
        exact variableChangePointAddEquiv E C0
      have hW1a₆ : W1.a₆ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₆_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hPaffE.1
      have hW1a₄ : W1.a₄ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₄_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hden
      have hW1a₃_formula : W1.a₃ = E.a₃ + E.a₁ * x₀ + 2 * y₀ := by
        simp [W1, C0]
      have hW1a₃_ne : W1.a₃ ≠ 0 := by
        rw [hW1a₃_formula]
        intro h
        apply hden
        linarith
      have hW1origin : WeierstrassCurve.Affine.Nonsingular W1 0 0 := by
        apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        rw [WeierstrassCurve.Affine.equation_iff]
        simp [hW1a₆]
      have hφ0P_origin :
          φ0 P₀ = WeierstrassCurve.Affine.Point.some 0 0 hW1origin := by
        change variableChangePointMap E C0 P₀ =
          WeierstrassCurve.Affine.Point.some 0 0 hW1origin
        dsimp [variableChangePointMap, P₀]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor <;>
          simp [C0, variableChangePointX,
            variableChangePointY, translateToOriginTangent]
      have hW1a₂_ne : W1.a₂ ≠ 0 := by
        intro hW1a₂
        have h3zero_origin :
            (3 : ℕ) •
                (WeierstrassCurve.Affine.Point.some 0 0 hW1origin :
                  WeierstrassCurve.Affine.Point W1) = 0 :=
          origin_three_nsmul_eq_zero_of_a2_eq_zero
            W1 hW1a₂ hW1a₃_ne hW1a₄ hW1a₆
        have h3zero_map : (3 : ℕ) • φ0 P₀ = 0 := by
          simpa [hφ0P_origin] using h3zero_origin
        have h3zero : (3 : ℕ) • P₀ = 0 := by
          apply (EquivLike.injective φ0)
          rw [map_nsmul, h3zero_map, map_zero]
        exact Psmall₀ 3 hn (by norm_num) h3zero
      let ρ : ℚ := W1.a₃ / W1.a₂
      have hρ : ρ ≠ 0 := div_ne_zero hW1a₃_ne hW1a₂_ne
      let C1 := scaleByRho ρ hρ
      let b : ℚ := tateBFromCoefficients W1.a₂ W1.a₃
      let c : ℚ := tateCFromCoefficients W1.a₁ W1.a₂ W1.a₃
      have hW2eq : C1 • W1 = tateNormalFormCurve b c := by
        ext <;> dsimp [C1, ρ, b, c, tateNormalFormCurve,
          tateBFromCoefficients, tateCFromCoefficients]
        · rw [WeierstrassCurve.variableChange_a₁]
          simp [scaleByRho]
          field_simp [hW1a₂_ne, hW1a₃_ne]
        · rw [scaleByTateRho_a₂ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · rw [scaleByTateRho_a₃ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · simp [WeierstrassCurve.variableChange_a₄, scaleByRho, hW1a₄]
        · simp [WeierstrassCurve.variableChange_a₆, scaleByRho, hW1a₆]
      haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := by
        rw [← hW2eq]
        infer_instance
      let φ1raw : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (C1 • W1) :=
        variableChangePointAddEquiv W1 C1
      let φ1 : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
        φ1raw.trans (pointCurveEqAddEquiv hW2eq)
      have hφ1φ0P_origin : φ1 (φ0 P₀) = tateOrigin b c := by
        rw [hφ0P_origin]
        have hRawOrigin :
            WeierstrassCurve.Affine.Nonsingular (C1 • W1) 0 0 := by
          simpa [hW2eq] using tate_origin_nonsingular b c
        have hφ1raw_origin :
            φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
              WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin := by
          change variableChangePointMap W1 C1
              (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
            WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin
          dsimp [variableChangePointMap]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor <;>
            simp [C1, variableChangePointX, variableChangePointY, scaleByRho]
        change (pointCurveEqAddEquiv hW2eq)
            (φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin)) =
          tateOrigin b c
        rw [hφ1raw_origin]
        exact pointCurveEqAddEquiv_some hW2eq
      have hOriginOrder : addOrderOf (tateOrigin b c) = n := by
        have hmaporder : addOrderOf (φ1 (φ0 P₀)) = n := by
          calc
            addOrderOf (φ1 (φ0 P₀)) = addOrderOf (φ0 P₀) :=
              addOrderOf_injective φ1.toAddMonoidHom
                (EquivLike.injective φ1) (φ0 P₀)
            _ = addOrderOf P₀ :=
              addOrderOf_injective φ0.toAddMonoidHom
                (EquivLike.injective φ0) P₀
            _ = n := hP₀_order
        rwa [hφ1φ0P_origin] at hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W1.a₂ ^ 3 / W1.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW1a₂_ne) (pow_ne_zero 2 hW1a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      have hj : (tateNormalFormCurve b c).j = E.j := by
        have hjraw : (C1 • W1).j = E.j := by simp [W1]
        simpa only [hW2eq] using hjraw
      exact ⟨b, c, inferInstance, hOriginOrder, hb, hj⟩

/-- The Tate-normal-form bridge with only the order and nonvanishing data. -/
theorem exists_tate_normalized_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 := by
  obtain ⟨b, c, hEll, hord, hb, _hj⟩ :=
    exists_tate_normalized_of_addOrder_gt_three_with_j E P n hn hP
  exact ⟨b, c, hEll, hord, hb⟩

end

end MazurProof.TateNormalFormBridge

end

open scoped WeierstrassCurve.Affine

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ, b ≠ 0 ∧
      ∃ _hEll : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic,
        ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).j = E.j ∧
        ∃ h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0,
          addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = n := by
  obtain ⟨b, c, hEll, hord, hb, hj⟩ :=
    MazurProof.TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three_with_j E P n hn hP
  exact ⟨b, c, hb, hEll, hj,
    @MazurProof.TateNormalFormBridge.tate_origin_nonsingular b c hEll, hord⟩
