-- Prove2me | solution 1 for MazurHuang.eq_zero_or_eq_neg_four_of_X1_eleven_equation
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:28.171316+00:00
-- url     : https://prove2.me/submissions/89e02c03-8d33-4021-b3c1-b9ca3d786bef

/-
Rational points of the modular curve X_1(11) (Billing-Mahler).

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * division-polynomial interface derived from three Proved platform theorems (glue)
  * scratch/TateZ2xZ10.lean
  * scratch/TateZ2xZ10Reduction.lean (point transport along Weierstrass variable changes)
  * FLT/Assumptions/MazurProof/RationalPointsN11Descent.lean
  * FLT/Assumptions/MazurProof/BillingMahlerField.lean
  * FLT/Assumptions/MazurProof/RationalPointsN11IdealSquare.lean
  * FLT/Assumptions/MazurProof/RationalPointsN11.lean lines 16-22 (the two definitions)
  * FLT/Assumptions/MazurProof/CyclicExclusion11.lean lines 247-529 (the Billing-Mahler assembly)
  * the published statement
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq

/-!
## Division-polynomial interface

The fork proves the two statements `KeystoneLadder.xRep_nsmul_same_xPair` and
`KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval` below by its own x-only Montgomery-ladder /
elliptic-divisibility-sequence development (13 modules `scratch.Ward*`, `scratch.Psi*`,
`scratch.Keystone*`).  The platform library already holds Proved theorems that contain these
facts in greater generality:

* `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` (`n • P = 0 ↔ ψₙ(P) = 0`),
* `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` (`x(nP) = Φₙ(x) / Ψₙ²(x)`),
* `WeierstrassCurve.isCoprime_Phi_PsiSq` (`Φₙ` and `Ψₙ²` are coprime).

This section re-derives the fork's two interface statements, with their original wording, from
those three theorems, so that the remaining source modules are used unchanged.  The hypotheses
`h4`, `hψ_ne`, `hc3` of the fork's statements are kept for source compatibility and are not used.
`SameP1Vec`, its two lemmas and `xPair` are copied from `scratch/KeystoneLadder.lean`.
-/
section KeystoneInterface

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace KeystoneLadder

variable {k : Type*} [Field k]

/-- Projective equality on Mathlib's `Fin 2` representatives, oriented as `v = c • u`
for a nonzero scalar `c`. This stronger orientation excludes the zero vector on the right. -/
def SameP1Vec (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1Vec

lemma second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1Vec (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by
  rcases h with ⟨c, _hc, rfl⟩
  simp

lemma second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1Vec (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩
  simpa using hc

end SameP1Vec

/-- The division-polynomial representative `[Φₙ(x) : Ψₙ²(x)]` of `x(nP)`. -/
noncomputable def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-- On the curve, `ψₙ(x, y)² = Ψₙ²(x)`: the evaluation at a point of Mathlib's identities
`CoordinateRing.mk_ψ` and `CoordinateRing.mk_Ψ_sq` in the coordinate ring. -/
private theorem evalEval_ψ_sq_eq (V : WeierstrassCurve k) {x y : k}
    (h : V.toAffine.Equation x y) (n : ℤ) :
    (V.ψ n).evalEval x y ^ 2 = (V.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk V (V.ψ n * V.ψ n) =
      Affine.CoordinateRing.mk V (C (V.ΨSq n)) := by
    rw [map_mul, Affine.CoordinateRing.mk_ψ, ← sq, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (V.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  rw [sq]
  exact h1

/-- The projective x-coordinate formula `x(nP) = [Φₙ(x) : Ψₙ²(x)]`, for a curve given directly
(no base change), assembled from the three platform theorems. -/
private theorem xRep_nsmul_same_xPair_core (V : WeierstrassCurve k) [V.IsElliptic]
    {n : ℕ} {x y : k} (h : V.toAffine.Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : V.toAffine.Point)).xRep)
      (xPair V (n : ℤ) x) := by
  have hsq := evalEval_ψ_sq_eq V h.1 (n : ℤ)
  by_cases hψ : (V.ψ (n : ℤ)).evalEval x y = 0
  · have hzero : n • (Point.some x y h : V.toAffine.Point) = 0 := by
      rw [← natCast_zsmul]
      exact (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff V h (n : ℤ)).mpr hψ
    have hΨ : (V.ΨSq (n : ℤ)).eval x = 0 := by
      rw [← hsq, hψ]
      exact zero_pow two_ne_zero
    have hΦ : (V.Φ (n : ℤ)).eval x ≠ 0 := by
      obtain ⟨a, b, hab⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq V (n : ℤ)
      intro hΦ0
      have h1 := congrArg (Polynomial.eval x) hab
      rw [eval_add, eval_mul, eval_mul, hΦ0, hΨ, mul_zero, mul_zero, add_zero, eval_one] at h1
      exact zero_ne_one h1
    rw [hzero, Point.xRep_zero]
    refine ⟨(V.Φ (n : ℤ)).eval x, hΦ, ?_⟩
    simp only [xPair, hΨ, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul, mul_one, mul_zero]
  · obtain ⟨y', h', hP⟩ :=
      WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div V h hψ
    have hΨ : (V.ΨSq (n : ℤ)).eval x ≠ 0 := by
      rw [← hsq]
      exact pow_ne_zero 2 hψ
    have hcross : (V.Φ (n : ℤ)).eval x =
        (V.ΨSq (n : ℤ)).eval x * ((V.Φ (n : ℤ)).eval x / (V.ΨSq (n : ℤ)).eval x) := by
      field_simp
    rw [← natCast_zsmul, hP, Point.xRep_some]
    refine ⟨(V.ΨSq (n : ℤ)).eval x, hΨ, ?_⟩
    simp only [xPair, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul, mul_one, ← hcross]

/-- The projective division-polynomial coordinate formula (statement as in
`scratch/KeystoneEDS.lean`). -/
theorem xRep_nsmul_same_xPair (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : (W⁄k).Point)).xRep)
      (xPair W (n : ℤ) x) := by
  have hW : W.baseChange k = W := by
    first
      | exact W.map_id
      | (ext <;> simp [WeierstrassCurve.baseChange])
  have key : ∀ (V : WeierstrassCurve k) (_hV : V = W) (h' : V.toAffine.Nonsingular x y),
      SameP1Vec ((n • (Point.some x y h' : V.toAffine.Point)).xRep) (xPair W (n : ℤ) x) := by
    intro V hV h'
    subst hV
    exact xRep_nsmul_same_xPair_core V h'
  exact key (W.baseChange k) hW h

/-- Keystone target reduced to the projective division-polynomial coordinate formula
(statement and proof as in `scratch/KeystoneEDS.lean`). -/
theorem nsmul_eq_zero_iff_ΨSq_eval (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : (W⁄k).Point := Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
      xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
    have hsecond :=
      SameP1Vec.second_eq_zero_of_same_infty (v := xPair W (n : ℤ) x) (by
        simpa [P, hn] using hsame)
    simpa [xPair] using hsecond
  · intro hψ
    by_contra hn
    cases hnp : n • P with
    | zero =>
        exact hn hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
          xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
        have hsecond_ne :
            (xPair W (n : ℤ) x) 1 ≠ 0 :=
          SameP1Vec.second_ne_zero_of_same_affine
            (x := xn) (v := xPair W (n : ℤ) x) (by
              simpa [hnp] using hsame)
        exact hsecond_ne (by simpa [xPair] using hψ)

end KeystoneLadder

end KeystoneInterface

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

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsN11Descent.lean (whole module, imports dropped). -/
section

/-!
# The parity tail in the Billing--Mahler descent for 11a3

Billing and Mahler reduce the non-torsion part of the rational-point problem
for the order-11 modular curve to integral coefficients satisfying, among
other identities,

`18 z² = c² + 2ab + 4bc`,

where `z` is odd and `a` is even.  Modulo four this says that a square is
congruent to two.  This file verifies that final obstruction independently of
the still-missing cubic-field descent which produces the coefficients.
-/

namespace MazurProof.RationalPointsN11Descent

/-! ## The integral cubic used by Billing and Mahler -/

def MordellEquation (ξ η : ℚ) : Prop :=
  η ^ 2 = ξ ^ 3 - 432 * ξ + 8208

/-- The affine model `Y²=X³+8X²+16X+16` maps to the integral cubic by
`ξ=9X+24`, `η=27Y`. -/
theorem mordellEquation_of_E11
    {X Y : ℚ} (hE11 : Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16) :
    MordellEquation (9 * X + 24) (27 * Y) := by
  unfold MordellEquation
  linear_combination 729 * hE11

/-- The denominator of the monic cubic is the cube of the denominator of
its argument. -/
private theorem den_mordell_cubic (u : ℚ) :
    ((u ^ 3 - 432 * u + 8208).den : ℤ) = (u.den : ℤ) ^ 3 := by
  set a : ℤ := u.num
  set d : ℤ := (u.den : ℤ)
  have hdpos : (0 : ℤ) < d := by positivity
  have hdne : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hdpos)
  have hred : IsCoprime a d := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [a, d, Int.natAbs_natCast]
    exact u.reduced
  set N : ℤ := a ^ 3 - 432 * a * d ^ 2 + 8208 * d ^ 3
  have hNd : IsCoprime N d := by
    have h1 : IsCoprime (a ^ 3) d := hred.pow_left
    have h2 : IsCoprime
        (a ^ 3 + d * (-432 * a * d + 8208 * d ^ 2)) d :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hNd3 : IsCoprime N (d ^ 3) := hNd.pow_right
  have hNd3_nat : Nat.Coprime N.natAbs (d ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hNd3
  have hrepr : u ^ 3 - 432 * u + 8208 = (N : ℚ) / (d ^ 3 : ℚ) := by
    have hu : u = (a : ℚ) / (d : ℚ) := by
      simp only [a, d]
      push_cast
      exact (Rat.num_div_den u).symm
    rw [hu]
    field_simp [hdne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hNd3_nat

/-- A rational point on the integral cubic has a square denominator in its
first coordinate. -/
theorem mordell_rat_denom_square (ξ η : ℚ)
    (h : MordellEquation ξ η) :
    ∃ x z : ℤ, 0 < z ∧ Int.gcd x z = 1 ∧
      ξ = (x : ℚ) / (z : ℚ) ^ 2 := by
  have hsq : IsSquare (ξ ^ 3 - 432 * ξ + 8208) := by
    refine ⟨η, ?_⟩
    rw [← h]
    ring
  have hden_sq : IsSquare (ξ ^ 3 - 432 * ξ + 8208).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hden_eq : (ξ ^ 3 - 432 * ξ + 8208).den = ξ.den ^ 3 := by
    exact_mod_cast den_mordell_cubic ξ
  have hden3_sq : IsSquare (ξ.den ^ 3) := hden_eq ▸ hden_sq
  have hden_sq' : IsSquare ξ.den := by
    rcases hden3_sq with ⟨w, hw⟩
    have hdvd : ξ.den ^ 2 ∣ w ^ 2 := ⟨ξ.den, by rw [sq w, ← hw]; ring⟩
    have hdvdw : ξ.den ∣ w := by
      rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
        Nat.ceilRoot_pow_self two_ne_zero] at hdvd
    obtain ⟨v, rfl⟩ := hdvdw
    refine ⟨v, mul_left_cancel₀ (pow_ne_zero 2 ξ.den_ne_zero) ?_⟩
    calc
      ξ.den ^ 2 * ξ.den = ξ.den ^ 3 := by ring
      _ = ξ.den * v * (ξ.den * v) := hw
      _ = ξ.den ^ 2 * (v * v) := by ring
  obtain ⟨z₀, hz₀⟩ := hden_sq'
  have hz₀pos : 0 < z₀ := by
    rcases Nat.eq_zero_or_pos z₀ with hz | hz
    · simp [hz] at hz₀
    · exact hz
  refine ⟨ξ.num, (z₀ : ℤ), by exact_mod_cast hz₀pos, ?_, ?_⟩
  · have hzdiv : z₀ ∣ ξ.den := ⟨z₀, hz₀⟩
    have := ξ.reduced.coprime_dvd_right hzdiv
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      ξ = (ξ.num : ℚ) / (ξ.den : ℚ) := by
        simpa using (Rat.num_div_den ξ).symm
      _ = (ξ.num : ℚ) / ((z₀ : ℚ) ^ 2) := by
        rw [hz₀]
        push_cast
        ring

/-- Clearing the square denominator gives the primitive integral cubic used
in the descent. -/
theorem mordell_integral_model_of_rational_point (ξ η : ℚ)
    (h : MordellEquation ξ η) :
    ∃ x z y : ℤ,
      0 < z ∧ Int.gcd x z = 1 ∧
        ξ = (x : ℚ) / (z : ℚ) ^ 2 ∧
        y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 := by
  obtain ⟨x, z, hzpos, hcop, hξ⟩ := mordell_rat_denom_square ξ η h
  have hz : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hzpos)
  have hrat : (η * (z : ℚ) ^ 3) ^ 2 =
      ((x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 : ℤ) : ℚ) := by
    unfold MordellEquation at h
    rw [hξ] at h
    push_cast at h ⊢
    field_simp [hz] at h ⊢
    nlinarith
  have hsquare : IsSquare
      ((x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 : ℤ) : ℚ) :=
    ⟨η * (z : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsquare
  obtain ⟨y, hy⟩ := hsquare
  refine ⟨x, z, y, hzpos, hcop, hξ, ?_⟩
  rw [sq y]
  linarith

/-! ## The finite exceptional-point certificate -/

def mordellDiscriminantAbs : ℕ := 1496537856

private def squareMod (m : ℕ) (n : ℤ) : Bool :=
  decide (∃ r : Fin m,
    (r.1 : ℤ) ^ 2 % (m : ℤ) = n % (m : ℤ))

private theorem squareMod_of_sq (m : ℕ) (hm : 0 < m) (x y : ℤ)
    (h : y ^ 2 = x) : squareMod m x = true := by
  simp only [squareMod, decide_eq_true_eq]
  have hmInt : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hryNonneg : 0 ≤ y % (m : ℤ) :=
    Int.emod_nonneg y (ne_of_gt hmInt)
  have hryLt : y % (m : ℤ) < (m : ℤ) :=
    Int.emod_lt_of_pos y hmInt
  have hryCast : (((y % (m : ℤ)).toNat : ℕ) : ℤ) = y % (m : ℤ) :=
    Int.toNat_of_nonneg hryNonneg
  have hryNatLt : (y % (m : ℤ)).toNat < m := by
    exact_mod_cast (hryCast ▸ hryLt)
  refine ⟨⟨(y % (m : ℤ)).toNat, hryNatLt⟩, ?_⟩
  rw [hryCast, ← h]
  simp [pow_two, Int.mul_emod]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
-- Kernel reduction checks 1227 candidates against eleven small moduli.
/-- Exhaustive bounded check of the integral cubic.  The first coordinate is
in `[-27,1199]` by elementary inequalities.  For each of these 1227 integers
we use quadratic-residue filters modulo `16,3,5,...,31`. -/
private theorem exceptional_integral_points_certificate :
    ∀ i : Fin 1227,
      let x : ℤ := (i.1 : ℤ) - 27
      let value := x ^ 3 - 432 * x + 8208
      squareMod 16 value = true →
      squareMod 3 value = true →
      squareMod 5 value = true →
      squareMod 7 value = true →
      squareMod 11 value = true →
      squareMod 13 value = true →
      squareMod 17 value = true →
      squareMod 19 value = true →
      squareMod 23 value = true →
      squareMod 29 value = true →
      squareMod 31 value = true →
      x = -12 ∨ x = 24 := by
  decide

/-- The finite half of the Billing--Mahler argument: an integral point whose
ordinate satisfies the Lutz--Nagell discriminant divisibility condition is
one of the four affine boundary points. -/
theorem exceptional_integral_point_boundary
    (x y : ℤ)
    (hcurve : y ^ 2 = x ^ 3 - 432 * x + 8208)
    (hy : y ^ 2 = 0 ∨ y ^ 2 ∣ (mordellDiscriminantAbs : ℤ)) :
    x = -12 ∨ x = 24 := by
  have hyBound : y ^ 2 ≤ (mordellDiscriminantAbs : ℤ) := by
    rcases hy with hy0 | hyD
    · rw [hy0]
      exact_mod_cast (Nat.zero_le mordellDiscriminantAbs)
    · have hyNatD : y.natAbs ^ 2 ∣ mordellDiscriminantAbs := by
        simpa [Int.natAbs_pow, mordellDiscriminantAbs] using
          (Int.natAbs_dvd_natAbs.mpr hyD)
      have hyNatLe : y.natAbs ^ 2 ≤ mordellDiscriminantAbs :=
        Nat.le_of_dvd (by norm_num [mordellDiscriminantAbs]) hyNatD
      have hyCast : (y.natAbs : ℤ) ^ 2 ≤
          (mordellDiscriminantAbs : ℤ) := by
        exact_mod_cast hyNatLe
      have hySq : y ^ 2 = (y.natAbs : ℤ) ^ 2 := by
        simp only [Int.natCast_natAbs, sq_abs]
      rw [hySq]
      exact hyCast
  have hxLower : -27 ≤ x := by
    by_contra hnot
    have hx28 : x + 28 ≤ 0 := by omega
    have hquad : 0 ≤ x ^ 2 - 28 * x + 352 := by
      nlinarith [sq_nonneg (x - 14)]
    have hprod : (x + 28) * (x ^ 2 - 28 * x + 352) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hx28 hquad
    have hid : x ^ 3 - 432 * x + 8208 =
        (x + 28) * (x ^ 2 - 28 * x + 352) - 1648 := by
      ring
    nlinarith [sq_nonneg y]
  have hxUpper : x ≤ 1199 := by
    change y ^ 2 ≤ 1496537856 at hyBound
    by_contra hnot
    have hx1200 : 0 ≤ x - 1200 := by omega
    have hquad : 0 ≤ x ^ 2 + 1200 * x + 1439568 := by
      nlinarith [sq_nonneg x]
    have hprod : 0 ≤ (x - 1200) * (x ^ 2 + 1200 * x + 1439568) :=
      mul_nonneg hx1200 hquad
    have hid : x ^ 3 - 432 * x + 8208 =
        (x - 1200) * (x ^ 2 + 1200 * x + 1439568) + 1727489808 := by
      ring
    nlinarith
  have hxShiftNonneg : 0 ≤ x + 27 := by omega
  have hxShiftEq : (((x + 27).toNat : ℕ) : ℤ) = x + 27 := by
    exact Int.toNat_of_nonneg hxShiftNonneg
  have hxShiftLt : (x + 27).toNat < 1227 := by
    omega
  let i : Fin 1227 := ⟨(x + 27).toNat, hxShiftLt⟩
  let value : ℤ := ((i.1 : ℤ) - 27) ^ 3 -
    432 * ((i.1 : ℤ) - 27) + 8208
  have hvalue : y ^ 2 = value := by
    dsimp [value, i]
    rw [hxShiftEq]
    norm_num
    exact hcurve
  have hcert := exceptional_integral_points_certificate i
    (squareMod_of_sq 16 (by norm_num) value y hvalue)
    (squareMod_of_sq 3 (by norm_num) value y hvalue)
    (squareMod_of_sq 5 (by norm_num) value y hvalue)
    (squareMod_of_sq 7 (by norm_num) value y hvalue)
    (squareMod_of_sq 11 (by norm_num) value y hvalue)
    (squareMod_of_sq 13 (by norm_num) value y hvalue)
    (squareMod_of_sq 17 (by norm_num) value y hvalue)
    (squareMod_of_sq 19 (by norm_num) value y hvalue)
    (squareMod_of_sq 23 (by norm_num) value y hvalue)
    (squareMod_of_sq 29 (by norm_num) value y hvalue)
    (squareMod_of_sq 31 (by norm_num) value y hvalue)
  simpa [i, hxShiftEq] using hcert

/-! ## The final parity obstruction -/

private theorem zmod_four_square_ne_two (u : ZMod 4) : u ^ 2 ≠ 2 := by
  fin_cases u <;> decide

/-- The final mod-4 contradiction in the Billing--Mahler descent. -/
theorem no_billing_mahler_middle_equation
    (z a b c : ℤ) (hz : Odd z) (ha : Even a)
    (hmid : 18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c) : False := by
  rcases hz with ⟨z₀, hz⟩
  rcases ha with ⟨a₀, ha⟩
  rw [hz, ha] at hmid
  have hmid4 := congrArg (fun q : ℤ ↦ (q : ZMod 4)) hmid
  push_cast at hmid4
  ring_nf at hmid4
  rw [show (4 : ZMod 4) = 0 by decide,
    show (18 : ZMod 4) = 2 by decide,
    show (72 : ZMod 4) = 0 by decide] at hmid4
  simp only [mul_zero, zero_add, add_zero] at hmid4
  have hc : (c : ZMod 4) ^ 2 = 2 := by
    exact hmid4.symm
  exact zmod_four_square_ne_two (c : ZMod 4) hc

/-- The three coefficient identities in the Billing--Mahler cubic-field
descent are inconsistent for a primitive pair `(x,z)`.  In particular, the
parity hypotheses used by `no_billing_mahler_middle_equation` are consequences,
not additional descent assumptions. -/
theorem no_billing_mahler_coefficient_system
    (x z a b c : ℤ)
    (hcop : Int.gcd x z = 1)
    (hfirst : -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c)
    (hmid : 18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c)
    (hthird : x = 2 * (b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2)) : False := by
  have hxEven : Even x := by
    refine ⟨b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2, ?_⟩
    rw [hthird]
    ring
  rcases hxEven with ⟨x₀, hx₀⟩
  have haSqEven : Even (a ^ 2) := by
    refine ⟨-x₀ + 12 * z ^ 2 - 2 * b * c, ?_⟩
    rw [hx₀] at hfirst
    nlinarith
  have haEven : Even a :=
    (Int.even_pow' (m := a) (n := 2) (by norm_num)).mp haSqEven
  have hxEven : Even x := ⟨x₀, hx₀⟩
  have hzOdd : Odd z := by
    rcases Int.even_or_odd z with hzEven | hzOdd
    · have hcop' : IsCoprime x z :=
        (Int.isCoprime_iff_gcd_eq_one).mpr hcop
      have hunit : IsUnit (2 : ℤ) :=
        hcop'.isUnit_of_dvd' hxEven.two_dvd hzEven.two_dvd
      rw [Int.isUnit_iff] at hunit
      norm_num at hunit
    · exact hzOdd
  exact no_billing_mahler_middle_equation z a b c hzOdd haEven hmid

end MazurProof.RationalPointsN11Descent

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/BillingMahlerField.lean (whole module, imports dropped). -/
section

/-!
# The cubic field in the Billing--Mahler order-11 descent

This file develops the explicit cubic field generated by an element `alpha`
with

`alpha^3 - 4 * alpha^2 + 4 * alpha - 2 = 0`.

If `theta^3 - 4 * theta - 4 = 0`, then `alpha = theta^2 / 2` and
`theta = alpha^2 - 2 * alpha`.  The power basis `1, alpha, alpha^2`
is therefore the integral basis `1, theta, theta^2 / 2` used by Billing
and Mahler, only in a more convenient order.
-/

namespace MazurProof.BillingMahlerField

open Polynomial
open Module
open NumberField.InfinitePlace
open scoped NumberField

noncomputable def cubicPolyInt : ℤ[X] :=
  X ^ 3 - 4 * X ^ 2 + 4 * X - 2

noncomputable def cubicPoly : ℚ[X] :=
  cubicPolyInt.map (algebraMap ℤ ℚ)

private lemma cubicPolyInt_monic : cubicPolyInt.Monic := by
  unfold cubicPolyInt
  monicity!

private lemma cubicPolyInt_natDegree : cubicPolyInt.natDegree = 3 := by
  unfold cubicPolyInt
  compute_degree!

private lemma cubicPolyInt_eisenstein_two :
    cubicPolyInt.IsEisensteinAt (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hPne : P ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  refine cubicPolyInt_monic.isEisensteinAt_of_mem_of_notMem hPne ?_ ?_
  · intro n hn
    rw [cubicPolyInt_natDegree] at hn
    interval_cases n <;>
      norm_num [cubicPolyInt, coeff_X_pow, coeff_X, P, Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [cubicPolyInt]

private lemma cubicPolyInt_irreducible : Irreducible cubicPolyInt := by
  apply cubicPolyInt_eisenstein_two.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  · exact cubicPolyInt_monic.isPrimitive
  · rw [cubicPolyInt_natDegree]
    norm_num

theorem cubicPoly_irreducible : Irreducible cubicPoly := by
  exact (cubicPolyInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
    cubicPolyInt_irreducible

instance cubicPolyIrreducibleFact : Fact (Irreducible cubicPoly) :=
  ⟨cubicPoly_irreducible⟩

theorem cubicPoly_monic : cubicPoly.Monic := by
  rw [cubicPoly]
  exact cubicPolyInt_monic.map (algebraMap ℤ ℚ)

theorem cubicPoly_natDegree : cubicPoly.natDegree = 3 := by
  rw [cubicPoly, cubicPolyInt_monic.natDegree_map (algebraMap ℤ ℚ)]
  exact cubicPolyInt_natDegree

abbrev K : Type := AdjoinRoot cubicPoly

noncomputable def alpha : K := AdjoinRoot.root cubicPoly

noncomputable def powerBasis : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis cubicPolyIrreducibleFact.out.ne_zero

noncomputable def basis : Basis (Fin 3) ℚ K :=
  powerBasis.basis.reindex (finCongr (by simpa [powerBasis] using cubicPoly_natDegree))

@[simp] theorem powerBasis_gen : powerBasis.gen = alpha := rfl

theorem basis_apply (i : Fin 3) : basis i = alpha ^ (i : ℕ) := by
  -- port v4.33.1: `simp` leaves `root ^ ↑((finCongr _).symm i) = root ^ ↑i`
  -- (it no longer sees through the `finCongr` index coercion); that goal is `rfl`.
  simp only [basis, powerBasis, alpha, Basis.coe_reindex, Function.comp_apply,
    AdjoinRoot.powerBasis_gen, PowerBasis.coe_basis]
  rfl

theorem finrank_K : Module.finrank ℚ K = 3 := by
  rw [PowerBasis.finrank powerBasis]
  simpa [powerBasis] using cubicPoly_natDegree

theorem cubicPoly_eq : cubicPoly = X ^ 3 - 4 * X ^ 2 + 4 * X - 2 := by
  ext n
  simp [cubicPoly, cubicPolyInt]

theorem alpha_relation : alpha ^ 3 - 4 * alpha ^ 2 + 4 * alpha - 2 = 0 := by
  change AdjoinRoot.mk cubicPoly (X ^ 3 - 4 * X ^ 2 + 4 * X - 2) = 0
  rw [← cubicPoly_eq, AdjoinRoot.mk_self]

theorem alpha_cubed : alpha ^ 3 = 4 * alpha ^ 2 - 4 * alpha + 2 := by
  linear_combination alpha_relation

theorem alpha_fourth : alpha ^ 4 = 12 * alpha ^ 2 - 14 * alpha + 8 := by
  calc
    alpha ^ 4 = alpha * alpha ^ 3 := by ring
    _ = alpha * (4 * alpha ^ 2 - 4 * alpha + 2) := by rw [alpha_cubed]
    _ = 4 * alpha ^ 3 - 4 * alpha ^ 2 + 2 * alpha := by ring
    _ = 12 * alpha ^ 2 - 14 * alpha + 8 := by
      rw [alpha_cubed]
      ring

noncomputable def ofCoords (a b c : ℚ) : K :=
  algebraMap ℚ K a + algebraMap ℚ K b * alpha + algebraMap ℚ K c * alpha ^ 2

private theorem ofCoords_eq_basis_sum (a b c : ℚ) :
    ofCoords a b c =
      a • basis (0 : Fin 3) + b • basis (1 : Fin 3) + c • basis (2 : Fin 3) := by
  simp [ofCoords, basis_apply, Algebra.smul_def]

@[simp] theorem basis_repr_ofCoords_zero (a b c : ℚ) :
    basis.repr (ofCoords a b c) (0 : Fin 3) = a := by
  rw [ofCoords_eq_basis_sum]
  simp

@[simp] theorem basis_repr_ofCoords_one (a b c : ℚ) :
    basis.repr (ofCoords a b c) (1 : Fin 3) = b := by
  rw [ofCoords_eq_basis_sum]
  simp

@[simp] theorem basis_repr_ofCoords_two (a b c : ℚ) :
    basis.repr (ofCoords a b c) (2 : Fin 3) = c := by
  rw [ofCoords_eq_basis_sum]
  simp

theorem exists_ofCoords (u : K) : ∃ a b c : ℚ, u = ofCoords a b c := by
  let a := basis.repr u (0 : Fin 3)
  let b := basis.repr u (1 : Fin 3)
  let c := basis.repr u (2 : Fin 3)
  refine ⟨a, b, c, ?_⟩
  apply basis.repr.injective
  ext i
  fin_cases i <;> simp [a, b, c]

theorem ofCoords_injective : Function.Injective (fun p : ℚ × ℚ × ℚ ↦
    ofCoords p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have hrepr := congrArg basis.repr h
  have hzero := congrArg (fun f ↦ f (0 : Fin 3)) hrepr
  have hone := congrArg (fun f ↦ f (1 : Fin 3)) hrepr
  have htwo := congrArg (fun f ↦ f (2 : Fin 3)) hrepr
  exact Prod.ext (by simpa using hzero) <| Prod.ext (by simpa using hone) (by simpa using htwo)

theorem ofCoords_sq (a b c : ℚ) :
    ofCoords a b c ^ 2 = ofCoords
      (a ^ 2 + 4 * b * c + 8 * c ^ 2)
      (2 * a * b - 8 * b * c - 14 * c ^ 2)
      (b ^ 2 + 2 * a * c + 8 * b * c + 12 * c ^ 2) := by
  unfold ofCoords
  push_cast
  ring_nf
  rw [alpha_fourth, alpha_cubed]
  norm_num
  ring

noncomputable def epsilon : K := alpha - 1

theorem epsilon_mul_inverse :
    epsilon * (alpha ^ 2 - 3 * alpha + 1) = 1 := by
  unfold epsilon
  linear_combination alpha_relation

theorem alpha_isIntegral : IsIntegral ℤ alpha := by
  refine ⟨cubicPolyInt, cubicPolyInt_monic, ?_⟩
  simpa [cubicPolyInt, alpha] using alpha_relation

theorem epsilon_isIntegral : IsIntegral ℤ epsilon :=
  alpha_isIntegral.sub isIntegral_one

noncomputable def epsilonInteger : NumberField.RingOfIntegers K :=
  ⟨epsilon, epsilon_isIntegral⟩

@[simp] theorem epsilonInteger_coe_K :
    ((epsilonInteger : NumberField.RingOfIntegers K) : K) = epsilon :=
  rfl

noncomputable def epsilonUnit : (NumberField.RingOfIntegers K)ˣ where
  val := epsilonInteger
  inv := ⟨alpha ^ 2 - 3 * alpha + 1,
    by
      have h : IsIntegral ℤ (alpha ^ 2 - 3 • alpha + 1) :=
        (alpha_isIntegral.pow 2).sub (alpha_isIntegral.nsmul 3) |>.add isIntegral_one
      exact (mem_integralClosure_iff ℤ K).mpr (by simpa [nsmul_eq_mul] using h)⟩
  val_inv := Subtype.ext epsilon_mul_inverse
  -- port v4.33.1: `rw [mul_comm]` now picks the product `3 * alpha` inside the subtype
  -- proof term (motive not type correct); state the commuted equation as a term instead.
  inv_val := Subtype.ext ((mul_comm _ _).trans epsilon_mul_inverse)

@[simp] theorem epsilonUnit_coe_integer :
    ((epsilonUnit : (NumberField.RingOfIntegers K)ˣ) :
      NumberField.RingOfIntegers K) = epsilonInteger :=
  rfl

@[simp] theorem epsilonUnit_coe_K :
    ((epsilonUnit : (NumberField.RingOfIntegers K)ˣ) : K) = epsilon :=
  -- port v4.33.1: `simp` stops at `algebraMap (𝓞 K) K ⟨epsilon, _⟩`; the equation is `rfl`.
  rfl

/-! ## The power-basis discriminant -/

noncomputable def minpolyDerivativeValue : K :=
  3 * alpha ^ 2 - 8 * alpha + 4

private theorem minpolyDerivativeValue_mul_basis_zero :
    minpolyDerivativeValue * basis (0 : Fin 3) = ofCoords 4 (-8) 3 := by
  simp [minpolyDerivativeValue, basis_apply, ofCoords]
  ring

private theorem minpolyDerivativeValue_mul_basis_one :
    minpolyDerivativeValue * basis (1 : Fin 3) = ofCoords 6 (-8) 4 := by
  rw [basis_apply]
  norm_num
  unfold minpolyDerivativeValue ofCoords
  push_cast
  ring_nf
  rw [alpha_cubed]
  norm_num
  ring

private theorem minpolyDerivativeValue_mul_basis_two :
    minpolyDerivativeValue * basis (2 : Fin 3) = ofCoords 8 (-10) 8 := by
  rw [basis_apply]
  norm_num
  unfold minpolyDerivativeValue ofCoords
  push_cast
  ring_nf
  rw [alpha_fourth, alpha_cubed]
  norm_num
  ring

private theorem repr_minpolyDerivativeValue_mul_basis_zero (i : Fin 3) :
    basis.repr (minpolyDerivativeValue * basis (0 : Fin 3)) i =
      ![(4 : ℚ), -8, 3] i := by
  rw [minpolyDerivativeValue_mul_basis_zero]
  fin_cases i
  · simpa using basis_repr_ofCoords_zero (4 : ℚ) (-8) 3
  · simpa using basis_repr_ofCoords_one (4 : ℚ) (-8) 3
  · simpa using basis_repr_ofCoords_two (4 : ℚ) (-8) 3

private theorem repr_minpolyDerivativeValue_mul_basis_one (i : Fin 3) :
    basis.repr (minpolyDerivativeValue * basis (1 : Fin 3)) i =
      ![(6 : ℚ), -8, 4] i := by
  rw [minpolyDerivativeValue_mul_basis_one]
  fin_cases i
  · simpa using basis_repr_ofCoords_zero (6 : ℚ) (-8) 4
  · simpa using basis_repr_ofCoords_one (6 : ℚ) (-8) 4
  · simpa using basis_repr_ofCoords_two (6 : ℚ) (-8) 4

private theorem repr_minpolyDerivativeValue_mul_basis_two (i : Fin 3) :
    basis.repr (minpolyDerivativeValue * basis (2 : Fin 3)) i =
      ![(8 : ℚ), -10, 8] i := by
  rw [minpolyDerivativeValue_mul_basis_two]
  fin_cases i
  · simpa using basis_repr_ofCoords_zero (8 : ℚ) (-10) 8
  · simpa using basis_repr_ofCoords_one (8 : ℚ) (-10) 8
  · simpa using basis_repr_ofCoords_two (8 : ℚ) (-10) 8

private theorem leftMulMatrix_entry_zero_zero :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (0 : Fin 3) (0 : Fin 3) = 4 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_zero 0

private theorem leftMulMatrix_entry_one_zero :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (1 : Fin 3) (0 : Fin 3) = -8 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_zero 1

private theorem leftMulMatrix_entry_two_zero :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (2 : Fin 3) (0 : Fin 3) = 3 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_zero 2

private theorem leftMulMatrix_entry_zero_one :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (0 : Fin 3) (1 : Fin 3) = 6 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_one 0

private theorem leftMulMatrix_entry_one_one :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (1 : Fin 3) (1 : Fin 3) = -8 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_one 1

private theorem leftMulMatrix_entry_two_one :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (2 : Fin 3) (1 : Fin 3) = 4 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_one 2

private theorem leftMulMatrix_entry_zero_two :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (0 : Fin 3) (2 : Fin 3) = 8 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_two 0

private theorem leftMulMatrix_entry_one_two :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (1 : Fin 3) (2 : Fin 3) = -10 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_two 1

private theorem leftMulMatrix_entry_two_two :
    Algebra.leftMulMatrix basis minpolyDerivativeValue (2 : Fin 3) (2 : Fin 3) = 8 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  exact repr_minpolyDerivativeValue_mul_basis_two 2

theorem norm_minpolyDerivativeValue :
    Algebra.norm ℚ minpolyDerivativeValue = 44 := by
  rw [Algebra.norm_eq_matrix_det basis, Matrix.det_fin_three,
    leftMulMatrix_entry_zero_zero, leftMulMatrix_entry_zero_one,
    leftMulMatrix_entry_zero_two, leftMulMatrix_entry_one_zero,
    leftMulMatrix_entry_one_one, leftMulMatrix_entry_one_two,
    leftMulMatrix_entry_two_zero, leftMulMatrix_entry_two_one,
    leftMulMatrix_entry_two_two]
  norm_num

private theorem alpha_mul_basis_zero :
    alpha * basis (0 : Fin 3) = ofCoords 0 1 0 := by
  simp [basis_apply, ofCoords]

private theorem alpha_mul_basis_one :
    alpha * basis (1 : Fin 3) = ofCoords 0 0 1 := by
  simp [basis_apply, ofCoords]
  norm_num
  ring_nf

private theorem alpha_mul_basis_two :
    alpha * basis (2 : Fin 3) = ofCoords 2 (-4) 4 := by
  rw [basis_apply]
  norm_num
  unfold ofCoords
  push_cast
  ring_nf
  rw [alpha_cubed]
  norm_num
  ring_nf

private theorem alpha_sq_mul_basis_zero :
    alpha ^ 2 * basis (0 : Fin 3) = ofCoords 0 0 1 := by
  simp [basis_apply, ofCoords]

private theorem alpha_sq_mul_basis_one :
    alpha ^ 2 * basis (1 : Fin 3) = ofCoords 2 (-4) 4 := by
  rw [basis_apply]
  norm_num
  unfold ofCoords
  push_cast
  ring_nf
  rw [alpha_cubed]
  norm_num
  ring_nf

private theorem alpha_sq_mul_basis_two :
    alpha ^ 2 * basis (2 : Fin 3) = ofCoords 8 (-14) 12 := by
  rw [basis_apply]
  norm_num
  unfold ofCoords
  push_cast
  ring_nf
  rw [alpha_fourth]
  norm_num
  ring_nf

private theorem leftMulMatrix_alpha_zero_zero :
    Algebra.leftMulMatrix basis alpha (0 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_mul_basis_zero]
  exact basis_repr_ofCoords_zero 0 1 0

private theorem leftMulMatrix_alpha_one_one :
    Algebra.leftMulMatrix basis alpha (1 : Fin 3) (1 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_mul_basis_one]
  exact basis_repr_ofCoords_one 0 0 1

private theorem leftMulMatrix_alpha_two_two :
    Algebra.leftMulMatrix basis alpha (2 : Fin 3) (2 : Fin 3) = 4 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_mul_basis_two]
  exact basis_repr_ofCoords_two 2 (-4) 4

private theorem leftMulMatrix_alpha_sq_zero_zero :
    Algebra.leftMulMatrix basis (alpha ^ 2) (0 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_sq_mul_basis_zero]
  exact basis_repr_ofCoords_zero 0 0 1

private theorem leftMulMatrix_alpha_sq_one_one :
    Algebra.leftMulMatrix basis (alpha ^ 2) (1 : Fin 3) (1 : Fin 3) = -4 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_sq_mul_basis_one]
  exact basis_repr_ofCoords_one 2 (-4) 4

private theorem leftMulMatrix_alpha_sq_two_two :
    Algebra.leftMulMatrix basis (alpha ^ 2) (2 : Fin 3) (2 : Fin 3) = 12 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, alpha_sq_mul_basis_two]
  exact basis_repr_ofCoords_two 8 (-14) 12

private theorem trace_one : Algebra.trace ℚ K 1 = 3 := by
  simpa using Algebra.trace_algebraMap_of_basis basis (1 : ℚ)

private theorem trace_alpha : Algebra.trace ℚ K alpha = 4 := by
  rw [Algebra.trace_eq_matrix_trace basis, Matrix.trace_fin_three,
    leftMulMatrix_alpha_zero_zero, leftMulMatrix_alpha_one_one,
    leftMulMatrix_alpha_two_two]
  norm_num

private theorem trace_alpha_sq : Algebra.trace ℚ K (alpha ^ 2) = 8 := by
  rw [Algebra.trace_eq_matrix_trace basis, Matrix.trace_fin_three,
    leftMulMatrix_alpha_sq_zero_zero, leftMulMatrix_alpha_sq_one_one,
    leftMulMatrix_alpha_sq_two_two]
  norm_num

private theorem trace_alpha_cubed : Algebra.trace ℚ K (alpha ^ 3) = 22 := by
  rw [alpha_cubed]
  have hrewrite : 4 * alpha ^ 2 - 4 * alpha + 2 =
      (4 : ℚ) • alpha ^ 2 - (4 : ℚ) • alpha + (2 : ℚ) • (1 : K) := by
    simp [Algebra.smul_def]
  rw [hrewrite, map_add, map_sub, map_smul, map_smul, map_smul,
    trace_alpha_sq, trace_alpha, trace_one]
  norm_num

private theorem trace_alpha_fourth : Algebra.trace ℚ K (alpha ^ 4) = 64 := by
  rw [alpha_fourth]
  have hrewrite : 12 * alpha ^ 2 - 14 * alpha + 8 =
      (12 : ℚ) • alpha ^ 2 - (14 : ℚ) • alpha + (8 : ℚ) • (1 : K) := by
    simp [Algebra.smul_def]
  rw [hrewrite, map_add, map_sub, map_smul, map_smul, map_smul,
    trace_alpha_sq, trace_alpha, trace_one]
  norm_num

private theorem traceMatrix_zero_zero : Algebra.traceMatrix ℚ basis 0 0 = 3 := by
  change Algebra.trace ℚ K (basis 0 * basis 0) = 3
  simpa [basis_apply] using trace_one

private theorem traceMatrix_zero_one : Algebra.traceMatrix ℚ basis 0 1 = 4 := by
  change Algebra.trace ℚ K (basis 0 * basis 1) = 4
  simpa [basis_apply] using trace_alpha

private theorem traceMatrix_zero_two : Algebra.traceMatrix ℚ basis 0 2 = 8 := by
  change Algebra.trace ℚ K (basis 0 * basis 2) = 8
  simpa [basis_apply] using trace_alpha_sq

private theorem traceMatrix_one_zero : Algebra.traceMatrix ℚ basis 1 0 = 4 := by
  change Algebra.trace ℚ K (basis 1 * basis 0) = 4
  simpa [basis_apply] using trace_alpha

private theorem traceMatrix_one_one : Algebra.traceMatrix ℚ basis 1 1 = 8 := by
  change Algebra.trace ℚ K (basis 1 * basis 1) = 8
  simpa [basis_apply, pow_two] using trace_alpha_sq

private theorem traceMatrix_one_two : Algebra.traceMatrix ℚ basis 1 2 = 22 := by
  change Algebra.trace ℚ K (basis 1 * basis 2) = 22
  convert trace_alpha_cubed using 1 <;> simp [basis_apply] <;> ring_nf

private theorem traceMatrix_two_zero : Algebra.traceMatrix ℚ basis 2 0 = 8 := by
  change Algebra.trace ℚ K (basis 2 * basis 0) = 8
  simpa [basis_apply] using trace_alpha_sq

private theorem traceMatrix_two_one : Algebra.traceMatrix ℚ basis 2 1 = 22 := by
  change Algebra.trace ℚ K (basis 2 * basis 1) = 22
  convert trace_alpha_cubed using 1 <;> simp [basis_apply] <;> ring_nf

private theorem traceMatrix_two_two : Algebra.traceMatrix ℚ basis 2 2 = 64 := by
  change Algebra.trace ℚ K (basis 2 * basis 2) = 64
  convert trace_alpha_fourth using 1 <;> simp [basis_apply] <;> ring_nf

theorem basis_discr : Algebra.discr ℚ basis = -44 := by
  rw [Algebra.discr_def, Matrix.det_fin_three,
    traceMatrix_zero_zero, traceMatrix_zero_one, traceMatrix_zero_two,
    traceMatrix_one_zero, traceMatrix_one_one, traceMatrix_one_two,
    traceMatrix_two_zero, traceMatrix_two_one, traceMatrix_two_two]
  norm_num

/-! ## Bounding the field discriminant and the class number -/

noncomputable def integralIndexEquiv :
    Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ Fin 3 :=
  Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis K),
      NumberField.RingOfIntegers.rank, finrank_K, Fintype.card_fin])

noncomputable def integralBasisFin : Basis (Fin 3) ℚ K :=
  (NumberField.integralBasis K).reindex integralIndexEquiv

theorem integralBasisFin_discr :
    Algebra.discr ℚ integralBasisFin = (NumberField.discr K : ℚ) := by
  simp only [integralBasisFin, Basis.coe_reindex]
  rw [Algebra.discr_reindex, ← NumberField.coe_discr]

noncomputable def basisInteger (i : Fin 3) : NumberField.RingOfIntegers K :=
  ⟨basis i, (mem_integralClosure_iff ℤ K).mpr <| by
    rw [basis_apply]
    exact alpha_isIntegral.pow i⟩

@[simp] theorem basisInteger_coe_K (i : Fin 3) :
    ((basisInteger i : NumberField.RingOfIntegers K) : K) = basis i :=
  rfl

private theorem integralBasisFin_repr_basis (i j : Fin 3) :
    integralBasisFin.repr (basis j) i =
      algebraMap ℤ ℚ
        ((NumberField.RingOfIntegers.basis K).repr (basisInteger j)
          (integralIndexEquiv.symm i)) := by
  rw [integralBasisFin, Basis.repr_reindex_apply]
  -- port v4.33.1: `simp` no longer reduces `algebraMap (𝓞 K) K ⟨basis j, _⟩` to `basis j`;
  -- rewrite it by an explicit `rfl` equation first.
  have h := NumberField.integralBasis_repr_apply K (basisInteger j) (integralIndexEquiv.symm i)
  have hc : (algebraMap (NumberField.RingOfIntegers K) K) (basisInteger j) = basis j := rfl
  rw [hc] at h
  simpa using h

private theorem integral_toMatrix_entries (i j : Fin 3) :
    IsIntegral ℤ (integralBasisFin.toMatrix basis i j) := by
  rw [Basis.toMatrix_apply, integralBasisFin_repr_basis]
  exact isIntegral_algebraMap

private theorem basis_discr_index_relation :
    ∃ d : ℤ, (-44 : ℤ) = d ^ 2 * NumberField.discr K := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := integralBasisFin.toMatrix basis
  have hdetInt : IsIntegral ℤ A.det :=
    IsIntegral.det fun i j ↦ integral_toMatrix_entries i j
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdetInt
  refine ⟨d, ?_⟩
  have hdisc := Algebra.discr_of_matrix_vecMul
    (A := ℚ) (B := K) (integralBasisFin : Fin 3 → K) A
  have hfamily :
      Matrix.vecMul (integralBasisFin : Fin 3 → K) (A.map (algebraMap ℚ K)) =
        (basis : Fin 3 → K) := by
    exact integralBasisFin.toMatrix_map_vecMul basis
  rw [hfamily, basis_discr, integralBasisFin_discr, ← hd] at hdisc
  apply Int.cast_injective (α := ℚ)
  push_cast
  exact hdisc

theorem natAbs_discr_le_44 : (NumberField.discr K).natAbs ≤ 44 := by
  obtain ⟨d, hd⟩ := basis_discr_index_relation
  have hdvd : NumberField.discr K ∣ (-44 : ℤ) := by
    refine ⟨d ^ 2, ?_⟩
    simpa [mul_comm] using hd
  exact Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num)

theorem abs_discr_le_44 : |NumberField.discr K| ≤ (44 : ℤ) := by
  have h : ((NumberField.discr K).natAbs : ℤ) ≤ (44 : ℤ) := by
    exact_mod_cast natAbs_discr_le_44
  simpa using h

theorem discr_neg : NumberField.discr K < 0 := by
  obtain ⟨d, hd⟩ := basis_discr_index_relation
  have hdne : d ≠ 0 := by
    intro hd0
    rw [hd0] at hd
    norm_num at hd
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  nlinarith

theorem nrComplexPlaces_eq_one : nrComplexPlaces K = 1 := by
  have hsign := NumberField.sign_discr K
  rw [Int.sign_eq_neg_one_of_neg discr_neg] at hsign
  have hodd : Odd (nrComplexPlaces K) := by
    exact (neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).mp hsign.symm
  have hdegree := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [finrank_K] at hdegree
  rcases hodd with ⟨r, hr⟩
  omega

theorem nrRealPlaces_eq_one : nrRealPlaces K = 1 := by
  have hdegree := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [finrank_K, nrComplexPlaces_eq_one] at hdegree
  omega

theorem infinitePlace_card_eq_two :
    Fintype.card (NumberField.InfinitePlace K) = 2 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_one, nrComplexPlaces_eq_one]

theorem unitRank_eq_one : NumberField.Units.rank K = 1 := by
  rw [NumberField.Units.rank, infinitePlace_card_eq_two]

theorem abs_discr_gt_eleven :
    (11 : ℝ) < |(NumberField.discr K : ℝ)| := by
  have hbound := NumberField.abs_discr_ge' K
  rw [finrank_K, nrComplexPlaces_eq_one] at hbound
  have hrewrite :
      (((3 : ℕ) : ℝ) ^ (2 * 3) /
          ((4 / Real.pi) ^ (2 * 1) * (Nat.factorial 3 : ℝ) ^ 2)) =
        81 * Real.pi ^ 2 / 64 := by
    norm_num [div_pow]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hrewrite] at hbound
  rw [Int.cast_abs] at hbound
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    have hprod : 0 < (Real.pi - 3) * (Real.pi + 3) :=
      mul_pos (sub_pos.mpr Real.pi_gt_three) (by linarith [Real.pi_pos])
    nlinarith
  linarith

theorem discr_eq_neg_44 : NumberField.discr K = -44 := by
  obtain ⟨d, hd⟩ := basis_discr_index_relation
  have hdne : d ≠ 0 := by
    intro hd0
    rw [hd0] at hd
    norm_num at hd
  have hdsqpos : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  have habsLower : (11 : ℤ) < |NumberField.discr K| := by
    exact_mod_cast abs_discr_gt_eleven
  have habsEq : (44 : ℤ) = d ^ 2 * |NumberField.discr K| := by
    rw [abs_of_neg discr_neg]
    nlinarith
  have hdsqLt : d ^ 2 < 4 := by
    by_contra hnot
    have hfour : (4 : ℤ) ≤ d ^ 2 := by omega
    have htwelve : (12 : ℤ) ≤ |NumberField.discr K| := by omega
    have hprod : 4 * 12 ≤ d ^ 2 * |NumberField.discr K| :=
      mul_le_mul hfour htwelve (by norm_num) (by positivity)
    rw [← habsEq] at hprod
    norm_num at hprod
  have hdLower : -2 < d := by nlinarith
  have hdUpper : d < 2 := by nlinarith
  have hdCases : d = -1 ∨ d = 1 := by omega
  rcases hdCases with rfl | rfl <;> norm_num at hd ⊢ <;> exact hd.symm

/-! The power basis is the full integral basis. -/

noncomputable def ringOfIntegersBasisFin :
    Basis (Fin 3) ℤ (NumberField.RingOfIntegers K) :=
  (NumberField.RingOfIntegers.basis K).reindex integralIndexEquiv

noncomputable def basisIntegerMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j ↦ ringOfIntegersBasisFin.repr (basisInteger j) i

private theorem ringOfIntegersBasisFin_repr_basisInteger (i j : Fin 3) :
    ringOfIntegersBasisFin.repr (basisInteger j) i =
      (NumberField.RingOfIntegers.basis K).repr (basisInteger j)
        (integralIndexEquiv.symm i) := by
  rw [ringOfIntegersBasisFin, Basis.repr_reindex_apply]

private theorem basisIntegerMatrix_map :
    basisIntegerMatrix.map (algebraMap ℤ ℚ) = integralBasisFin.toMatrix basis := by
  ext i j
  rw [Matrix.map_apply, basisIntegerMatrix, Basis.toMatrix_apply,
    ringOfIntegersBasisFin_repr_basisInteger]
  exact (integralBasisFin_repr_basis i j).symm

theorem basisIntegerMatrix_det_isUnit : IsUnit basisIntegerMatrix.det := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := integralBasisFin.toMatrix basis
  have hdisc := Algebra.discr_of_matrix_vecMul
    (A := ℚ) (B := K) (integralBasisFin : Fin 3 → K) A
  have hfamily :
      Matrix.vecMul (integralBasisFin : Fin 3 → K) (A.map (algebraMap ℚ K)) =
        (basis : Fin 3 → K) := by
    exact integralBasisFin.toMatrix_map_vecMul basis
  rw [hfamily, basis_discr, integralBasisFin_discr, discr_eq_neg_44] at hdisc
  norm_num at hdisc
  have hAdet : A.det ^ 2 = 1 := sq_eq_one_iff.mpr hdisc
  have hmapDet : algebraMap ℤ ℚ basisIntegerMatrix.det = A.det := by
    calc
      algebraMap ℤ ℚ basisIntegerMatrix.det =
          (basisIntegerMatrix.map (algebraMap ℤ ℚ)).det := by
            exact (algebraMap ℤ ℚ).map_det basisIntegerMatrix
      _ = A.det := by rw [basisIntegerMatrix_map]
  have hdetSq : basisIntegerMatrix.det ^ 2 = 1 := by
    apply Int.cast_injective (α := ℚ)
    change algebraMap ℤ ℚ (basisIntegerMatrix.det ^ 2) = algebraMap ℤ ℚ 1
    rw [map_pow, map_one, hmapDet, hAdet]
  rw [Int.isUnit_iff, ← sq_eq_one_iff]
  exact hdetSq

noncomputable def integralPowerBasis :
    Basis (Fin 3) ℤ (NumberField.RingOfIntegers K) :=
  ringOfIntegersBasisFin.map
    (Matrix.toLinearEquiv ringOfIntegersBasisFin basisIntegerMatrix
      basisIntegerMatrix_det_isUnit)

@[simp] theorem integralPowerBasis_apply (i : Fin 3) :
    integralPowerBasis i = basisInteger i := by
  simp only [integralPowerBasis, Basis.map_apply]
  change Matrix.toLin ringOfIntegersBasisFin ringOfIntegersBasisFin
      basisIntegerMatrix (ringOfIntegersBasisFin i) = basisInteger i
  rw [Matrix.toLin_self]
  simpa [basisIntegerMatrix] using
    ringOfIntegersBasisFin.sum_repr (basisInteger i)

@[simp] theorem integralPowerBasis_coe_K (i : Fin 3) :
    ((integralPowerBasis i : NumberField.RingOfIntegers K) : K) = basis i := by
  rw [integralPowerBasis_apply]
  rfl

theorem ringOfIntegers_exists_integer_coords
    (u : NumberField.RingOfIntegers K) :
    ∃ a b c : ℤ, (u : K) = ofCoords a b c := by
  let a := integralPowerBasis.repr u (0 : Fin 3)
  let b := integralPowerBasis.repr u (1 : Fin 3)
  let c := integralPowerBasis.repr u (2 : Fin 3)
  refine ⟨a, b, c, ?_⟩
  have hsum := integralPowerBasis.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  have hsumK := congrArg (fun v : NumberField.RingOfIntegers K ↦ (v : K)) hsum
  simpa [a, b, c, ofCoords, Algebra.smul_def, basis_apply] using hsumK.symm

/-! ## The explicit cubic factor in the Mordell equation -/

private theorem ofCoords_linear_mul_basis_zero (r q : ℚ) :
    ofCoords r q 0 * basis (0 : Fin 3) = ofCoords r q 0 := by
  simp [basis_apply]

private theorem ofCoords_linear_mul_basis_one (r q : ℚ) :
    ofCoords r q 0 * basis (1 : Fin 3) = ofCoords 0 r q := by
  simp [basis_apply, ofCoords]
  ring

private theorem ofCoords_linear_mul_basis_two (r q : ℚ) :
    ofCoords r q 0 * basis (2 : Fin 3) = ofCoords (2 * q) (-4 * q) (r + 4 * q) := by
  rw [basis_apply]
  norm_num
  unfold ofCoords
  push_cast
  ring_nf
  rw [alpha_cubed]
  norm_num
  ring

theorem norm_ofCoords_linear (r q : ℚ) :
    Algebra.norm ℚ (ofCoords r q 0) =
      r ^ 3 + 4 * r ^ 2 * q + 4 * r * q ^ 2 + 2 * q ^ 3 := by
  rw [Algebra.norm_eq_matrix_det basis, Matrix.det_fin_three]
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [ofCoords_linear_mul_basis_zero, ofCoords_linear_mul_basis_one,
    ofCoords_linear_mul_basis_two]
  simp
  ring

theorem norm_epsilon : Algebra.norm ℚ epsilon = 1 := by
  have hepsilon : epsilon = ofCoords (-1) 1 0 := by
    unfold epsilon ofCoords
    norm_num
    ring
  rw [hepsilon, norm_ofCoords_linear]
  norm_num

noncomputable def descentElement (x z : ℤ) : K :=
  ofCoords (x - 24 * z ^ 2) (18 * z ^ 2) 0

noncomputable def descentInteger (x z : ℤ) :
    NumberField.RingOfIntegers K :=
  (x - 24 * z ^ 2) • basisInteger (0 : Fin 3) +
    (18 * z ^ 2) • basisInteger (1 : Fin 3)

@[simp] theorem descentInteger_coe_K (x z : ℤ) :
    ((descentInteger x z : NumberField.RingOfIntegers K) : K) =
      descentElement x z := by
  simp [descentInteger, descentElement, ofCoords, basis_apply, Algebra.smul_def]
  norm_num [map_ofNat]

noncomputable def thetaBasisElement (a b c : ℤ) : K :=
  ofCoords a (c - 2 * b) b

theorem ringOfIntegers_exists_thetaBasis_coords
    (u : NumberField.RingOfIntegers K) :
    ∃ a b c : ℤ, (u : K) = thetaBasisElement a b c := by
  obtain ⟨p, q, r, hu⟩ := ringOfIntegers_exists_integer_coords u
  refine ⟨p, r, q + 2 * r, ?_⟩
  calc
    (u : K) = ofCoords p q r := hu
    _ = thetaBasisElement p r (q + 2 * r) := by
      unfold thetaBasisElement
      push_cast
      congr 1 <;> ring

theorem norm_descentElement (x z : ℤ) :
    Algebra.norm ℚ (descentElement x z) =
      ((x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6 : ℤ) : ℚ) := by
  rw [descentElement, norm_ofCoords_linear]
  push_cast
  ring

private theorem epsilon_mul_descentElement (x z : ℤ) :
    epsilon * descentElement x z =
      ofCoords (-x + 24 * z ^ 2) (x - 42 * z ^ 2) (18 * z ^ 2) := by
  unfold epsilon descentElement ofCoords
  push_cast
  norm_num
  ring_nf

private theorem thetaBasisElement_sq (a b c : ℤ) :
    thetaBasisElement a b c ^ 2 =
      ofCoords (a ^ 2 + 4 * b * c)
        (2 * a * c - 4 * a * b - 8 * b * c + 2 * b ^ 2)
        (c ^ 2 + 2 * a * b + 4 * b * c) := by
  unfold thetaBasisElement
  rw [ofCoords_sq]
  push_cast
  congr 1 <;> ring

/-- Expanding the Billing--Mahler square identity in the integral basis gives
the three integer equations used by the parity obstruction. -/
theorem coefficient_system_of_epsilon_mul_descentElement_eq_sq
    (x z a b c : ℤ)
    (h : epsilon * descentElement x z = thetaBasisElement a b c ^ 2) :
    -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c ∧
      18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c ∧
      x = 2 * (b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2) := by
  rw [epsilon_mul_descentElement, thetaBasisElement_sq] at h
  have hzero := congrArg (fun u : K ↦ basis.repr u (0 : Fin 3)) h
  have hone := congrArg (fun u : K ↦ basis.repr u (1 : Fin 3)) h
  have htwo := congrArg (fun u : K ↦ basis.repr u (2 : Fin 3)) h
  simp only [basis_repr_ofCoords_zero] at hzero
  simp only [basis_repr_ofCoords_one] at hone
  simp only [basis_repr_ofCoords_two] at htwo
  have hzeroInt : -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c := by
    exact_mod_cast hzero
  have htwoInt : 18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c := by
    exact_mod_cast htwo
  refine ⟨hzeroInt, htwoInt, ?_⟩
  have honeInt : x - 42 * z ^ 2 =
      2 * a * c - 4 * a * b - 8 * b * c + 2 * b ^ 2 := by
    exact_mod_cast hone
  nlinarith

theorem ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (NumberField.RingOfIntegers K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [finrank_K, nrComplexPlaces_eq_one]
  have habs : (|NumberField.discr K| : ℝ) ≤ 44 := by
    exact_mod_cast abs_discr_le_44
  have hpi := Real.pi_gt_three
  norm_num at ⊢
  nlinarith [sq_nonneg (Real.pi - 3)]

theorem classNumber_eq_one : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.mpr ringOfIntegers_isPrincipalIdealRing

/-- In a PID, a principal ideal that is an ideal square has a generator equal
to a unit times an element square. -/
theorem unit_mul_square_of_principal_ideal_square
    (d : NumberField.RingOfIntegers K)
    (I : Ideal (NumberField.RingOfIntegers K))
    (h : Ideal.span ({d} : Set (NumberField.RingOfIntegers K)) = I ^ 2) :
    ∃ u : (NumberField.RingOfIntegers K)ˣ,
      ∃ a : NumberField.RingOfIntegers K, d = (u : NumberField.RingOfIntegers K) * a ^ 2 := by
  letI : IsPrincipalIdealRing (NumberField.RingOfIntegers K) :=
    ringOfIntegers_isPrincipalIdealRing
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal I
  have hspan : Ideal.span ({d} : Set (NumberField.RingOfIntegers K)) =
      Ideal.span ({a ^ 2} : Set (NumberField.RingOfIntegers K)) := by
    calc
      Ideal.span ({d} : Set (NumberField.RingOfIntegers K)) = I ^ 2 := h
      _ = (Ideal.span ({a} : Set (NumberField.RingOfIntegers K))) ^ 2 := by rw [ha]
      _ = Ideal.span ({a ^ 2} : Set (NumberField.RingOfIntegers K)) := by
        rw [Ideal.span_singleton_pow]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u⁻¹, a, ?_⟩
  calc
    d = (d * (u : NumberField.RingOfIntegers K)) *
        (u⁻¹ : (NumberField.RingOfIntegers K)ˣ) := by simp
    _ = a ^ 2 * (u⁻¹ : (NumberField.RingOfIntegers K)ˣ) := by rw [hu]
    _ = ((u⁻¹ : (NumberField.RingOfIntegers K)ˣ) :
        NumberField.RingOfIntegers K) * a ^ 2 := by rw [mul_comm]

/-! ## The Billing--Mahler unit represents the nontrivial free squareclass -/

noncomputable def epsilonSquareShiftPolyInt : ℤ[X] :=
  X ^ 6 + 6 * X ^ 5 + 14 * X ^ 4 + 16 * X ^ 3 + 8 * X ^ 2 - 2

noncomputable def negEpsilonSquareShiftPolyInt : ℤ[X] :=
  X ^ 6 + 6 * X ^ 5 + 16 * X ^ 4 + 24 * X ^ 3 + 20 * X ^ 2 + 8 * X + 2

noncomputable def epsilonSquareShiftPoly : ℚ[X] :=
  epsilonSquareShiftPolyInt.map (algebraMap ℤ ℚ)

noncomputable def negEpsilonSquareShiftPoly : ℚ[X] :=
  negEpsilonSquareShiftPolyInt.map (algebraMap ℤ ℚ)

private theorem epsilonSquareShiftPolyInt_monic : epsilonSquareShiftPolyInt.Monic := by
  unfold epsilonSquareShiftPolyInt
  monicity!

private theorem negEpsilonSquareShiftPolyInt_monic : negEpsilonSquareShiftPolyInt.Monic := by
  unfold negEpsilonSquareShiftPolyInt
  monicity!

private theorem epsilonSquareShiftPolyInt_natDegree :
    epsilonSquareShiftPolyInt.natDegree = 6 := by
  unfold epsilonSquareShiftPolyInt
  compute_degree!

private theorem negEpsilonSquareShiftPolyInt_natDegree :
    negEpsilonSquareShiftPolyInt.natDegree = 6 := by
  unfold negEpsilonSquareShiftPolyInt
  compute_degree!

private theorem epsilonSquareShiftPolyInt_eisenstein_two :
    epsilonSquareShiftPolyInt.IsEisensteinAt
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hPne : P ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  refine epsilonSquareShiftPolyInt_monic.isEisensteinAt_of_mem_of_notMem hPne ?_ ?_
  · intro n hn
    rw [epsilonSquareShiftPolyInt_natDegree] at hn
    interval_cases n <;>
      norm_num [epsilonSquareShiftPolyInt, coeff_X_pow, coeff_X, P,
        Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [epsilonSquareShiftPolyInt]

private theorem negEpsilonSquareShiftPolyInt_eisenstein_two :
    negEpsilonSquareShiftPolyInt.IsEisensteinAt
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
  let P : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hPne : P ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    norm_num [Int.isUnit_iff]
  refine negEpsilonSquareShiftPolyInt_monic.isEisensteinAt_of_mem_of_notMem hPne ?_ ?_
  · intro n hn
    rw [negEpsilonSquareShiftPolyInt_natDegree] at hn
    interval_cases n <;>
      norm_num [negEpsilonSquareShiftPolyInt, coeff_X_pow, coeff_X, P,
        Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num [negEpsilonSquareShiftPolyInt]

private theorem epsilonSquareShiftPolyInt_irreducible :
    Irreducible epsilonSquareShiftPolyInt := by
  apply epsilonSquareShiftPolyInt_eisenstein_two.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  · exact epsilonSquareShiftPolyInt_monic.isPrimitive
  · rw [epsilonSquareShiftPolyInt_natDegree]
    norm_num

private theorem negEpsilonSquareShiftPolyInt_irreducible :
    Irreducible negEpsilonSquareShiftPolyInt := by
  apply negEpsilonSquareShiftPolyInt_eisenstein_two.irreducible
  · exact (Ideal.span_singleton_prime (by norm_num)).2 (by norm_num)
  · exact negEpsilonSquareShiftPolyInt_monic.isPrimitive
  · rw [negEpsilonSquareShiftPolyInt_natDegree]
    norm_num

theorem epsilonSquareShiftPoly_irreducible : Irreducible epsilonSquareShiftPoly := by
  exact
    (epsilonSquareShiftPolyInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
      epsilonSquareShiftPolyInt_irreducible

theorem negEpsilonSquareShiftPoly_irreducible :
    Irreducible negEpsilonSquareShiftPoly := by
  exact
    (negEpsilonSquareShiftPolyInt_monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mp
      negEpsilonSquareShiftPolyInt_irreducible

theorem epsilonSquareShiftPoly_monic : epsilonSquareShiftPoly.Monic := by
  rw [epsilonSquareShiftPoly]
  exact epsilonSquareShiftPolyInt_monic.map (algebraMap ℤ ℚ)

theorem negEpsilonSquareShiftPoly_monic : negEpsilonSquareShiftPoly.Monic := by
  rw [negEpsilonSquareShiftPoly]
  exact negEpsilonSquareShiftPolyInt_monic.map (algebraMap ℤ ℚ)

theorem epsilonSquareShiftPoly_natDegree : epsilonSquareShiftPoly.natDegree = 6 := by
  rw [epsilonSquareShiftPoly,
    epsilonSquareShiftPolyInt_monic.natDegree_map (algebraMap ℤ ℚ)]
  exact epsilonSquareShiftPolyInt_natDegree

theorem negEpsilonSquareShiftPoly_natDegree : negEpsilonSquareShiftPoly.natDegree = 6 := by
  rw [negEpsilonSquareShiftPoly,
    negEpsilonSquareShiftPolyInt_monic.natDegree_map (algebraMap ℤ ℚ)]
  exact negEpsilonSquareShiftPolyInt_natDegree

theorem epsilonSquareShiftPoly_eq : epsilonSquareShiftPoly =
    X ^ 6 + 6 * X ^ 5 + 14 * X ^ 4 + 16 * X ^ 3 + 8 * X ^ 2 - 2 := by
  ext n
  simp [epsilonSquareShiftPoly, epsilonSquareShiftPolyInt]

theorem negEpsilonSquareShiftPoly_eq : negEpsilonSquareShiftPoly =
    X ^ 6 + 6 * X ^ 5 + 16 * X ^ 4 + 24 * X ^ 3 + 20 * X ^ 2 + 8 * X + 2 := by
  ext n
  simp [negEpsilonSquareShiftPoly, negEpsilonSquareShiftPolyInt]

theorem epsilon_not_isSquare : ¬ IsSquare epsilon := by
  rintro ⟨u, hu⟩
  have hu2 : u ^ 2 = epsilon := by simpa [pow_two] using hu.symm
  have huAlpha : u ^ 2 + 1 = alpha := by
    rw [hu2]
    simp [epsilon]
  have hbase : u ^ 6 - u ^ 4 - u ^ 2 - 1 = 0 := by
    calc
      u ^ 6 - u ^ 4 - u ^ 2 - 1 =
          (u ^ 2 + 1) ^ 3 - 4 * (u ^ 2 + 1) ^ 2 + 4 * (u ^ 2 + 1) - 2 := by ring
      _ = alpha ^ 3 - 4 * alpha ^ 2 + 4 * alpha - 2 := by rw [huAlpha]
      _ = 0 := alpha_relation
  have hroot : aeval (u - 1) epsilonSquareShiftPoly = 0 := by
    calc
      aeval (u - 1) epsilonSquareShiftPoly =
          (u - 1) ^ 6 + 6 * (u - 1) ^ 5 + 14 * (u - 1) ^ 4 +
            16 * (u - 1) ^ 3 + 8 * (u - 1) ^ 2 - 2 := by
        rw [epsilonSquareShiftPoly_eq]
        simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
      _ = u ^ 6 - u ^ 4 - u ^ 2 - 1 := by ring
      _ = 0 := hbase
  have hmin := minpoly.eq_of_irreducible_of_monic
    epsilonSquareShiftPoly_irreducible hroot epsilonSquareShiftPoly_monic
  have hdegree : epsilonSquareShiftPoly.natDegree ≤ Module.finrank ℚ K := by
    rw [hmin]
    exact minpoly.natDegree_le (A := ℚ) (B := K) (u - 1)
  rw [epsilonSquareShiftPoly_natDegree, finrank_K] at hdegree
  omega

theorem neg_epsilon_not_isSquare : ¬ IsSquare (-epsilon) := by
  rintro ⟨u, hu⟩
  have hu2 : u ^ 2 = -epsilon := by simpa [pow_two] using hu.symm
  have huAlpha : 1 - u ^ 2 = alpha := by
    rw [hu2]
    simp [epsilon]
  have hbase : u ^ 6 + u ^ 4 - u ^ 2 + 1 = 0 := by
    calc
      u ^ 6 + u ^ 4 - u ^ 2 + 1 =
          -((1 - u ^ 2) ^ 3 - 4 * (1 - u ^ 2) ^ 2 + 4 * (1 - u ^ 2) - 2) := by ring
      _ = -(alpha ^ 3 - 4 * alpha ^ 2 + 4 * alpha - 2) := by rw [huAlpha]
      _ = 0 := by rw [alpha_relation]; ring
  have hroot : aeval (u - 1) negEpsilonSquareShiftPoly = 0 := by
    calc
      aeval (u - 1) negEpsilonSquareShiftPoly =
          (u - 1) ^ 6 + 6 * (u - 1) ^ 5 + 16 * (u - 1) ^ 4 +
            24 * (u - 1) ^ 3 + 20 * (u - 1) ^ 2 + 8 * (u - 1) + 2 := by
        rw [negEpsilonSquareShiftPoly_eq]
        simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
      _ = u ^ 6 + u ^ 4 - u ^ 2 + 1 := by ring
      _ = 0 := hbase
  have hmin := minpoly.eq_of_irreducible_of_monic
    negEpsilonSquareShiftPoly_irreducible hroot negEpsilonSquareShiftPoly_monic
  have hdegree : negEpsilonSquareShiftPoly.natDegree ≤ Module.finrank ℚ K := by
    rw [hmin]
    exact minpoly.natDegree_le (A := ℚ) (B := K) (u - 1)
  rw [negEpsilonSquareShiftPoly_natDegree, finrank_K] at hdegree
  omega

/-! ## Unit squareclasses -/

def fundamentalIndex : Fin (NumberField.Units.rank K) :=
  ⟨0, by simpa [unitRank_eq_one]⟩

noncomputable def fundamentalUnit :
    (NumberField.RingOfIntegers K)ˣ :=
  NumberField.Units.fundSystem K fundamentalIndex

private theorem unit_eq_torsion_mul_fundamental_zpow
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ ζ : NumberField.Units.torsion K, ∃ n : ℤ,
      u = (ζ : (NumberField.RingOfIntegers K)ˣ) * fundamentalUnit ^ n := by
  obtain ⟨⟨ζ, f⟩, hu, _hunique⟩ :=
    NumberField.Units.exist_unique_eq_mul_prod K u
  refine ⟨ζ, f fundamentalIndex, ?_⟩
  letI : Subsingleton (Fin (NumberField.Units.rank K)) :=
    Fintype.card_le_one_iff_subsingleton.mp (by simp [unitRank_eq_one])
  have hprod :
      ∏ i, NumberField.Units.fundSystem K i ^ f i =
        NumberField.Units.fundSystem K fundamentalIndex ^ f fundamentalIndex := by
    apply Fintype.prod_eq_single fundamentalIndex
    intro i hi
    exact (hi (Subsingleton.elim i fundamentalIndex)).elim
  rw [hprod] at hu
  simpa [fundamentalUnit] using hu

private theorem torsion_unit_eq_one_or_neg_one
    (ζ : NumberField.Units.torsion K) :
    (ζ : (NumberField.RingOfIntegers K)ˣ) = 1 ∨
      (ζ : (NumberField.RingOfIntegers K)ˣ) = -1 := by
  apply NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
  rw [finrank_K]
  norm_num [Odd]

private theorem isSquare_coe_K_of_unit
    {u : (NumberField.RingOfIntegers K)ˣ} (hu : IsSquare u) :
    IsSquare (((u : (NumberField.RingOfIntegers K)ˣ) :
      NumberField.RingOfIntegers K) : K) := by
  rcases hu with ⟨v, hv⟩
  refine ⟨(((v : (NumberField.RingOfIntegers K)ˣ) :
    NumberField.RingOfIntegers K) : K), ?_⟩
  simpa using congrArg
    (fun q : (NumberField.RingOfIntegers K)ˣ ↦
      (((q : (NumberField.RingOfIntegers K)ˣ) :
        NumberField.RingOfIntegers K) : K)) hv

theorem epsilon_fundamental_exponent_odd :
    ∃ ζ : NumberField.Units.torsion K, ∃ n : ℤ,
      Odd n ∧
        epsilonUnit = (ζ : (NumberField.RingOfIntegers K)ˣ) * fundamentalUnit ^ n := by
  obtain ⟨ζ, n, hepsilon⟩ := unit_eq_torsion_mul_fundamental_zpow epsilonUnit
  refine ⟨ζ, n, ?_, hepsilon⟩
  rcases Int.even_or_odd n with hnEven | hnOdd
  · have hfundSquare : IsSquare (fundamentalUnit ^ n) :=
      hnEven.isSquare_zpow fundamentalUnit
    rcases torsion_unit_eq_one_or_neg_one ζ with hζ | hζ
    · have hepsilonSquare : IsSquare epsilonUnit := by
        rw [hepsilon, hζ, one_mul]
        exact hfundSquare
      exact (epsilon_not_isSquare
        (by simpa using isSquare_coe_K_of_unit hepsilonSquare)).elim
    · have hnegEpsilonSquare : IsSquare (-epsilonUnit) := by
        rw [hepsilon, hζ]
        simpa using hfundSquare
      exact (neg_epsilon_not_isSquare
        (by simpa using isSquare_coe_K_of_unit hnegEpsilonSquare)).elim
  · exact hnOdd

/-- Every unit is represented modulo squares by one of
`1`, `-1`, `epsilon`, or `-epsilon`. -/
theorem unit_squareclass_classification
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ v : (NumberField.RingOfIntegers K)ˣ,
      u = v ^ 2 ∨ u = -(v ^ 2) ∨
        u = epsilonUnit * v ^ 2 ∨ u = -epsilonUnit * v ^ 2 := by
  obtain ⟨ζ, n, hu⟩ := unit_eq_torsion_mul_fundamental_zpow u
  obtain ⟨ζε, k, hkOdd, hε⟩ := epsilon_fundamental_exponent_odd
  rcases Int.even_or_odd n with hnEven | hnOdd
  · rcases hnEven.isSquare_zpow fundamentalUnit with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rcases torsion_unit_eq_one_or_neg_one ζ with hζ | hζ
    · left
      rw [hu, hζ, one_mul]
      simpa [pow_two] using hv
    · right; left
      rw [hu, hζ]
      simpa [pow_two] using congrArg Neg.neg hv
  · let τ : NumberField.Units.torsion K :=
      ⟨(ζ : (NumberField.RingOfIntegers K)ˣ) *
          (ζε : (NumberField.RingOfIntegers K)ˣ)⁻¹,
        ζ.property.mul ζε.property.inv⟩
    have hratio : u * epsilonUnit⁻¹ =
        (τ : (NumberField.RingOfIntegers K)ˣ) *
          fundamentalUnit ^ (n - k) := by
      rw [hu, hε]
      dsimp [τ]
      group
      exact mul_right_comm
        (ζ : (NumberField.RingOfIntegers K)ˣ)
        (fundamentalUnit ^ (n - k))
        ((ζε : (NumberField.RingOfIntegers K)ˣ) ^ (-1 : ℤ))
    have hdiffEven : Even (n - k) := hnOdd.sub_odd hkOdd
    rcases hdiffEven.isSquare_zpow fundamentalUnit with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rcases torsion_unit_eq_one_or_neg_one τ with hτ | hτ
    · right; right; left
      calc
        u = (u * epsilonUnit⁻¹) * epsilonUnit := by group
        _ = v ^ 2 * epsilonUnit := by rw [hratio, hτ, one_mul, hv, pow_two]
        _ = epsilonUnit * v ^ 2 := by ac_rfl
    · right; right; right
      calc
        u = (u * epsilonUnit⁻¹) * epsilonUnit := by group
        _ = -(v ^ 2) * epsilonUnit := by
          rw [hratio, hτ, hv, pow_two]
          simp
        _ = -epsilonUnit * v ^ 2 := by
          simp only [neg_mul, mul_neg]
          rw [mul_comm]

theorem unit_coe_K_squareclass_classification
    (u : (NumberField.RingOfIntegers K)ˣ) :
    ∃ v : K,
      (((u : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) = v ^ 2 ∨
      (((u : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) = -(v ^ 2) ∨
      (((u : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) = epsilon * v ^ 2 ∨
      (((u : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) = -epsilon * v ^ 2 := by
  obtain ⟨v, hv | hv | hv | hv⟩ := unit_squareclass_classification u
  all_goals
    refine ⟨(((v : (NumberField.RingOfIntegers K)ˣ) :
      NumberField.RingOfIntegers K) : K), ?_⟩
  · left
    simpa using congrArg
      (fun q : (NumberField.RingOfIntegers K)ˣ ↦
        (((q : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K)) hv
  · right; left
    simpa using congrArg
      (fun q : (NumberField.RingOfIntegers K)ˣ ↦
        (((q : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K)) hv
  · right; right; left
    simpa using congrArg
      (fun q : (NumberField.RingOfIntegers K)ˣ ↦
        (((q : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K)) hv
  · right; right; right
    simpa using congrArg
      (fun q : (NumberField.RingOfIntegers K)ˣ ↦
        (((q : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K)) hv

theorem descentInteger_four_squareclasses_of_ideal_square
    (x z : ℤ) (I : Ideal (NumberField.RingOfIntegers K))
    (h : Ideal.span ({descentInteger x z} :
      Set (NumberField.RingOfIntegers K)) = I ^ 2) :
    ∃ w : NumberField.RingOfIntegers K,
      descentInteger x z = w ^ 2 ∨
      descentInteger x z = -(w ^ 2) ∨
      descentInteger x z = epsilonInteger * w ^ 2 ∨
      descentInteger x z = -epsilonInteger * w ^ 2 := by
  obtain ⟨u, a, hd⟩ :=
    unit_mul_square_of_principal_ideal_square (descentInteger x z) I h
  obtain ⟨v, hu | hu | hu | hu⟩ := unit_squareclass_classification u
  · refine ⟨(v : NumberField.RingOfIntegers K) * a, Or.inl ?_⟩
    have huO : (u : NumberField.RingOfIntegers K) =
        (v : NumberField.RingOfIntegers K) ^ 2 := by
      simpa using congrArg
        (fun q : (NumberField.RingOfIntegers K)ˣ ↦
          (q : NumberField.RingOfIntegers K)) hu
    calc
      descentInteger x z = (u : NumberField.RingOfIntegers K) * a ^ 2 := hd
      _ = (v : NumberField.RingOfIntegers K) ^ 2 * a ^ 2 := by rw [huO]
      _ = ((v : NumberField.RingOfIntegers K) * a) ^ 2 := by ring
  · refine ⟨(v : NumberField.RingOfIntegers K) * a, Or.inr (Or.inl ?_)⟩
    have huO : (u : NumberField.RingOfIntegers K) =
        -((v : NumberField.RingOfIntegers K) ^ 2) := by
      simpa using congrArg
        (fun q : (NumberField.RingOfIntegers K)ˣ ↦
          (q : NumberField.RingOfIntegers K)) hu
    calc
      descentInteger x z = (u : NumberField.RingOfIntegers K) * a ^ 2 := hd
      _ = -((v : NumberField.RingOfIntegers K) ^ 2) * a ^ 2 := by rw [huO]
      _ = -(((v : NumberField.RingOfIntegers K) * a) ^ 2) := by ring
  · refine ⟨(v : NumberField.RingOfIntegers K) * a,
      Or.inr (Or.inr (Or.inl ?_))⟩
    have huO : (u : NumberField.RingOfIntegers K) =
        epsilonInteger * (v : NumberField.RingOfIntegers K) ^ 2 := by
      simpa using congrArg
        (fun q : (NumberField.RingOfIntegers K)ˣ ↦
          (q : NumberField.RingOfIntegers K)) hu
    calc
      descentInteger x z = (u : NumberField.RingOfIntegers K) * a ^ 2 := hd
      _ = (epsilonInteger * (v : NumberField.RingOfIntegers K) ^ 2) * a ^ 2 := by
        rw [huO]
      _ = epsilonInteger * ((v : NumberField.RingOfIntegers K) * a) ^ 2 := by ring
  · refine ⟨(v : NumberField.RingOfIntegers K) * a,
      Or.inr (Or.inr (Or.inr ?_))⟩
    have huO : (u : NumberField.RingOfIntegers K) =
        -epsilonInteger * (v : NumberField.RingOfIntegers K) ^ 2 := by
      simpa using congrArg
        (fun q : (NumberField.RingOfIntegers K)ˣ ↦
          (q : NumberField.RingOfIntegers K)) hu
    calc
      descentInteger x z = (u : NumberField.RingOfIntegers K) * a ^ 2 := hd
      _ = (-epsilonInteger * (v : NumberField.RingOfIntegers K) ^ 2) * a ^ 2 := by
        rw [huO]
      _ = -epsilonInteger * ((v : NumberField.RingOfIntegers K) * a) ^ 2 := by ring

/-- Once the principal ideal generated by the cubic factor is an ideal
square, the factor lies in one of the four unit squareclasses. -/
theorem descentElement_four_squareclasses_of_ideal_square
    (x z : ℤ) (I : Ideal (NumberField.RingOfIntegers K))
    (h : Ideal.span ({descentInteger x z} :
      Set (NumberField.RingOfIntegers K)) = I ^ 2) :
    ∃ w : K,
      descentElement x z = w ^ 2 ∨
      descentElement x z = -(w ^ 2) ∨
      descentElement x z = epsilon * w ^ 2 ∨
      descentElement x z = -epsilon * w ^ 2 := by
  obtain ⟨u, a, hd⟩ :=
    unit_mul_square_of_principal_ideal_square (descentInteger x z) I h
  have hdK : descentElement x z =
      (((u : (NumberField.RingOfIntegers K)ˣ) :
          NumberField.RingOfIntegers K) : K) *
        ((a : NumberField.RingOfIntegers K) : K) ^ 2 := by
    simpa using congrArg
      (fun q : NumberField.RingOfIntegers K ↦ (q : K)) hd
  obtain ⟨v, hu | hu | hu | hu⟩ := unit_coe_K_squareclass_classification u
  · refine ⟨v * (a : K), Or.inl ?_⟩
    calc
      descentElement x z =
          (((u : (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K) * (a : K) ^ 2 := hdK
      _ = v ^ 2 * (a : K) ^ 2 := by rw [hu]
      _ = (v * (a : K)) ^ 2 := by ring
  · refine ⟨v * (a : K), Or.inr (Or.inl ?_)⟩
    calc
      descentElement x z =
          (((u : (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K) * (a : K) ^ 2 := hdK
      _ = -(v ^ 2) * (a : K) ^ 2 := by rw [hu]
      _ = -((v * (a : K)) ^ 2) := by ring
  · refine ⟨v * (a : K), Or.inr (Or.inr (Or.inl ?_))⟩
    calc
      descentElement x z =
          (((u : (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K) * (a : K) ^ 2 := hdK
      _ = (epsilon * v ^ 2) * (a : K) ^ 2 := by rw [hu]
      _ = epsilon * (v * (a : K)) ^ 2 := by ring
  · refine ⟨v * (a : K), Or.inr (Or.inr (Or.inr ?_))⟩
    calc
      descentElement x z =
          (((u : (NumberField.RingOfIntegers K)ˣ) :
              NumberField.RingOfIntegers K) : K) * (a : K) ^ 2 := hdK
      _ = (-epsilon * v ^ 2) * (a : K) ^ 2 := by rw [hu]
      _ = -epsilon * (v * (a : K)) ^ 2 := by ring

private theorem norm_neg_square_nonpos (w : K) :
    Algebra.norm ℚ (-(w ^ 2)) ≤ 0 := by
  have hnorm : Algebra.norm ℚ (-(w ^ 2)) =
      -(Algebra.norm ℚ w) ^ 2 := by
    rw [show -(w ^ 2) = algebraMap ℚ K (-1) * w ^ 2 by simp,
      map_mul, Algebra.norm_algebraMap, map_pow, finrank_K]
    norm_num
  rw [hnorm]
  exact neg_nonpos.mpr (sq_nonneg _)

private theorem norm_neg_epsilon_square_nonpos (w : K) :
    Algebra.norm ℚ (-epsilon * w ^ 2) ≤ 0 := by
  have hnorm : Algebra.norm ℚ (-epsilon * w ^ 2) =
      -(Algebra.norm ℚ w) ^ 2 := by
    rw [show -epsilon = algebraMap ℚ K (-1) * epsilon by simp,
      mul_assoc, map_mul, map_mul, Algebra.norm_algebraMap, norm_epsilon,
      map_pow, finrank_K]
    norm_num
  rw [hnorm]
  exact neg_nonpos.mpr (sq_nonneg _)

theorem descentElement_eq_epsilon_mul_integral_sq_of_ideal_square
    (x z : ℤ) (I : Ideal (NumberField.RingOfIntegers K))
    (hideal : Ideal.span ({descentInteger x z} :
      Set (NumberField.RingOfIntegers K)) = I ^ 2)
    (hnonsquare : ¬ IsSquare (descentElement x z))
    (hnorm : 0 < Algebra.norm ℚ (descentElement x z)) :
    ∃ w : NumberField.RingOfIntegers K,
      descentElement x z = epsilon * ((w : NumberField.RingOfIntegers K) : K) ^ 2 := by
  obtain ⟨w, hw | hw | hw | hw⟩ :=
    descentInteger_four_squareclasses_of_ideal_square x z I hideal
  · have hwK : descentElement x z = ((w : NumberField.RingOfIntegers K) : K) ^ 2 := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers K ↦ (q : K)) hw
    exact (hnonsquare ⟨(w : K), by simpa [pow_two] using hwK⟩).elim
  · have hwK : descentElement x z = -(((w : NumberField.RingOfIntegers K) : K) ^ 2) := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers K ↦ (q : K)) hw
    have hnonpos := norm_neg_square_nonpos (w : K)
    rw [← hwK] at hnonpos
    linarith
  · refine ⟨w, ?_⟩
    simpa using congrArg
      (fun q : NumberField.RingOfIntegers K ↦ (q : K)) hw
  · have hwK : descentElement x z =
        -epsilon * ((w : NumberField.RingOfIntegers K) : K) ^ 2 := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers K ↦ (q : K)) hw
    have hnonpos := norm_neg_epsilon_square_nonpos (w : K)
    rw [← hwK] at hnonpos
    linarith

/-- A positive-norm nonsquare cubic factor whose principal ideal is an ideal
square is necessarily in the `epsilon` squareclass. -/
theorem descentElement_eq_epsilon_mul_sq_of_ideal_square
    (x z : ℤ) (I : Ideal (NumberField.RingOfIntegers K))
    (hideal : Ideal.span ({descentInteger x z} :
      Set (NumberField.RingOfIntegers K)) = I ^ 2)
    (hnonsquare : ¬ IsSquare (descentElement x z))
    (hnorm : 0 < Algebra.norm ℚ (descentElement x z)) :
    ∃ w : K, descentElement x z = epsilon * w ^ 2 := by
  obtain ⟨w, hw | hw | hw | hw⟩ :=
    descentElement_four_squareclasses_of_ideal_square x z I hideal
  · exact (hnonsquare ⟨w, by simpa [pow_two] using hw⟩).elim
  · have hnonpos := norm_neg_square_nonpos w
    rw [← hw] at hnonpos
    linarith
  · exact ⟨w, hw⟩
  · have hnonpos := norm_neg_epsilon_square_nonpos w
    rw [← hw] at hnonpos
    linarith

end MazurProof.BillingMahlerField

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsN11IdealSquare.lean (whole module, imports dropped). -/
section

/-!
# The ideal-square step in the Billing--Mahler descent

This file contains the prime-ideal bookkeeping for the cubic factor used in
the order-eleven descent.  The integral generator is the element `alpha` from
`BillingMahlerField`; its power basis is the full ring-of-integers basis, so
Dedekind--Kummer applies at every rational prime.
-/

namespace MazurProof.RationalPointsN11IdealSquare

open Polynomial
open scoped NumberField
open UniqueFactorizationMonoid
open scoped WeierstrassCurve.Affine
open Scratch.TateZ2xZ10Reduction

attribute [local instance] Ideal.Quotient.field

abbrev K := BillingMahlerField.K
abbrev OK := NumberField.RingOfIntegers K

abbrev ResidueInt (p : ℕ) := ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)

def mordellCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -432
  a₆ := 8208

theorem mordellCurve_delta : mordellCurve.Δ = (-23944605696 : ℚ) := by
  norm_num [mordellCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance mordellCurve_isElliptic : mordellCurve.IsElliptic where
  isUnit := by rw [mordellCurve_delta]; norm_num

def minimalCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1
  a₃ := 1
  a₄ := 0
  a₆ := 0

theorem minimalCurve_delta : minimalCurve.Δ = (-11 : ℚ) := by
  norm_num [minimalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance minimalCurve_isElliptic : minimalCurve.IsElliptic where
  isUnit := by rw [minimalCurve_delta]; norm_num

def mordellToMinimalChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 6 (by norm_num)
  r := -12
  s := 0
  t := 108

theorem mordellToMinimalChange_smul :
    mordellToMinimalChange • mordellCurve = minimalCurve := by
  ext <;> norm_num [mordellToMinimalChange, mordellCurve, minimalCurve,
    WeierstrassCurve.variableChange_def]

abbrev MinimalWeierstrass : WeierstrassCurve ℚ := minimalCurve

abbrev MinimalCurveBase : WeierstrassCurve.Affine ℚ := MinimalWeierstrass⁄ℚ

abbrev MinimalPoint := MinimalCurveBase.Point

private noncomputable def pointCurveEqAddEquiv
    [DecidableEq ℚ] {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+
      WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private noncomputable def affinePointCurveEqAddEquiv
    [DecidableEq ℚ] {W W' : WeierstrassCurve.Affine ℚ} (h : W = W') :
    W.Point ≃+ W'.Point := by
  subst h
  exact AddEquiv.refl _

private theorem pointCurveEqAddEquiv_some
    [DecidableEq ℚ] {W W' : WeierstrassCurve ℚ} (e : W = W')
    {x y : ℚ} (h : WeierstrassCurve.Affine.Nonsingular W x y) :
    ∃ h' : WeierstrassCurve.Affine.Nonsingular W' x y,
      pointCurveEqAddEquiv e
          (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some x y h' := by
  subst W'
  exact ⟨h, rfl⟩

private theorem affinePointCurveEqAddEquiv_some
    [DecidableEq ℚ] {W W' : WeierstrassCurve.Affine ℚ} (e : W = W')
    {x y : ℚ} (h : W.Nonsingular x y) :
    ∃ h' : W'.Nonsingular x y,
      affinePointCurveEqAddEquiv e
          (WeierstrassCurve.Affine.Point.some x y h) =
        WeierstrassCurve.Affine.Point.some x y h' := by
  subst W'
  exact ⟨h, rfl⟩

private theorem minimalCurveBase_eq :
    MinimalCurveBase = minimalCurve.toAffine := by
  ext <;> simp [MinimalCurveBase]

private theorem variableChange_slope_of_X_ne_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ} (hx : x1 ≠ x2) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

private theorem variableChange_slope_of_Y_ne_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ}
    (h1 : WeierstrassCurve.Affine.Equation W x1 y1)
    (h2 : WeierstrassCurve.Affine.Equation W x2 y2)
    (hx : x1 = x2) (hy : y1 ≠ WeierstrassCurve.Affine.negY W x2 y2) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  have hyEq : y1 = y2 :=
    WeierstrassCurve.Affine.Y_eq_of_Y_ne h1 h2 hx hy
  have hySelf : y1 ≠ WeierstrassCurve.Affine.negY W x1 y1 := by
    intro h
    apply hy
    rw [← hx, ← hyEq]
    exact h
  have hden : x1 * W.a₁ + W.a₃ + y1 * 2 ≠ 0 := by
    intro hden
    apply hySelf
    rw [WeierstrassCurve.Affine.negY]
    linarith
  have hmul :
      (x1 * W.a₁ + W.a₃ + y1 * 2) *
          (x1 * W.a₁ + W.a₃ + y1 * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htargetX :
      variableChangePointX C x1 = variableChangePointX C x2 := by
    simp [hx]
  have htargetY :
      variableChangePointY C x1 y1 ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x2) (variableChangePointY C x2 y2) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x1).mp
    rw [h, hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htargetX htargetY]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x1 * W.a₁ + W.a₃ + y1 * 2) *
          (x1 * W.a₁ + W.a₃ + y1 * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

private theorem variableChange_slope_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    {x1 x2 y1 y2 : ℚ}
    (h1 : WeierstrassCurve.Affine.Equation W x1 y1)
    (h2 : WeierstrassCurve.Affine.Equation W x2 y2)
    (hxy : ¬(x1 = x2 ∧ y1 = WeierstrassCurve.Affine.negY W x2 y2)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x1) (variableChangePointX C x2)
        (variableChangePointY C x1 y1) (variableChangePointY C x2 y2) =
      (C.u⁻¹ : ℚ) *
        (WeierstrassCurve.Affine.slope W x1 x2 y1 y2 - C.s) := by
  by_cases hx : x1 = x2
  · exact variableChange_slope_of_Y_ne_generic W C h1 h2 hx
      (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne_generic W C hx

private theorem variableChangePointMap_add_generic
    [DecidableEq ℚ]
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    (P Q : WeierstrassCurve.Affine.Point W) :
    Scratch.TateZ2xZ10Reduction.variableChangePointMap W C (P + Q) =
      Scratch.TateZ2xZ10Reduction.variableChangePointMap W C P +
        Scratch.TateZ2xZ10Reduction.variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x1 y1 h1 =>
    cases Q with
    | zero => rfl
    | some x2 y2 h2 =>
      by_cases hxy : x1 = x2 ∧
          y1 = WeierstrassCurve.Affine.negY W x2 y2
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq
          htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope_generic W C h1.left h2.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · let l : ℚ := WeierstrassCurve.Affine.slope W x1 x2 y1 y2
          let L : ℚ := WeierstrassCurve.Affine.slope (C • W)
            (variableChangePointX C x1) (variableChangePointX C x2)
            (variableChangePointY C x1 y1) (variableChangePointY C x2 y2)
          change variableChangePointX C
              (WeierstrassCurve.Affine.addX W x1 x2 l) =
            WeierstrassCurve.Affine.addX (C • W)
              (variableChangePointX C x1) (variableChangePointX C x2) L
          calc
            _ = WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                ((C.u : ℚ)⁻¹ * (l - C.s)) :=
              variableChange_addX W C x1 x2 l
            _ = _ := by
              apply congrArg (fun t : ℚ ↦ WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2) t)
              simpa only [l, L] using hslope.symm
        · let l : ℚ := WeierstrassCurve.Affine.slope W x1 x2 y1 y2
          let L : ℚ := WeierstrassCurve.Affine.slope (C • W)
            (variableChangePointX C x1) (variableChangePointX C x2)
            (variableChangePointY C x1 y1) (variableChangePointY C x2 y2)
          change variableChangePointY C
              (WeierstrassCurve.Affine.addX W x1 x2 l)
              (WeierstrassCurve.Affine.addY W x1 x2 y1 l) =
            WeierstrassCurve.Affine.addY (C • W)
              (variableChangePointX C x1) (variableChangePointX C x2)
              (variableChangePointY C x1 y1) L
          calc
            _ = WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                (variableChangePointY C x1 y1)
                ((C.u : ℚ)⁻¹ * (l - C.s)) :=
              variableChange_addY W C x1 x2 y1 l
            _ = _ := by
              apply congrArg (fun t : ℚ ↦ WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x1) (variableChangePointX C x2)
                (variableChangePointY C x1 y1) t)
              simpa only [l, L] using hslope.symm

noncomputable def mordellToMinimalPointAddEquiv [DecidableEq ℚ] :
    WeierstrassCurve.Affine.Point mordellCurve ≃+ MinimalPoint :=
  (AddEquiv.mk
    (Scratch.TateZ2xZ10Reduction.variableChangePointEquiv
      mordellCurve mordellToMinimalChange)
    (variableChangePointMap_add_generic mordellCurve mordellToMinimalChange)).trans
      ((pointCurveEqAddEquiv mordellToMinimalChange_smul).trans
        (affinePointCurveEqAddEquiv minimalCurveBase_eq.symm))

@[simp] theorem mordellCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation mordellCurve x y ↔
      y ^ 2 = x ^ 3 - 432 * x + 8208 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [mordellCurve]
  ring_nf

@[simp] theorem minimalCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation minimalCurve x y ↔
      y ^ 2 + y = x ^ 3 - x ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [minimalCurve]
  ring_nf

noncomputable def mordellPoint (x y : ℚ)
    (h : y ^ 2 = x ^ 3 - 432 * x + 8208) :
    WeierstrassCurve.Affine.Point mordellCurve :=
  WeierstrassCurve.Affine.Point.some x y
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff x y).2 h))

private theorem exists_mordell_half_of_line
    [DecidableEq ℚ]
    {xi eta u m n : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208)
    (h₂ : -m ^ 2 + 2 * u + xi = 0)
    (h₁ : -432 - 2 * m * n - u ^ 2 - 2 * xi * u = 0)
    (h₀ : 8208 - n ^ 2 + xi * u ^ 2 = 0)
    (hsign : m * xi + n = -eta) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = mordellPoint xi eta hcurve := by
  let v : ℚ := m * u + n
  have hQcurve : v ^ 2 = u ^ 3 - 432 * u + 8208 := by
    dsimp [v]
    linear_combination -(u ^ 2 * h₂ + u * h₁ + h₀)
  have htangent : 3 * u ^ 2 - 432 = 2 * m * v := by
    dsimp [v]
    linear_combination 2 * u * h₂ + h₁
  have hv : v ≠ 0 := by
    intro hv0
    have huSq : u ^ 2 = 12 ^ 2 := by
      rw [hv0] at htangent
      norm_num at htangent ⊢
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp huSq with hu | hu
    · norm_num [hu, hv0] at hQcurve
    · norm_num [hu, hv0] at hQcurve
  have hYne : v ≠ WeierstrassCurve.Affine.negY mordellCurve u v := by
    rw [WeierstrassCurve.Affine.negY]
    simp only [mordellCurve, zero_mul, zero_add]
    intro h
    apply hv
    linarith
  have hslope :
      WeierstrassCurve.Affine.slope mordellCurve u u v v = m := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hYne]
    simp [WeierstrassCurve.Affine.negY, mordellCurve]
    field_simp [hv]
    nlinarith [htangent]
  let hQ : WeierstrassCurve.Affine.Nonsingular mordellCurve u v :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff u v).2 hQcurve)
  let Q : WeierstrassCurve.Affine.Point mordellCurve :=
    WeierstrassCurve.Affine.Point.some u v hQ
  refine ⟨Q, ?_⟩
  rw [two_nsmul]
  change
    (WeierstrassCurve.Affine.Point.some u v hQ :
      WeierstrassCurve.Affine.Point mordellCurve) +
        WeierstrassCurve.Affine.Point.some u v hQ = _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hQ) hYne]
  unfold mordellPoint
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · simp only [hslope]
    simp [WeierstrassCurve.Affine.addX, mordellCurve]
    nlinarith [h₂]
  · simp only [hslope]
    simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
      mordellCurve, mordellPoint]
    dsimp [v]
    linear_combination m * h₂ - hsign

/-- The explicit Kummer-exactness direction for the Billing--Mahler cubic:
if the cubic factor of a point on the short Mordell model is a square, then
the point has a rational half. -/
theorem exists_mordell_half_of_factor_square
    [DecidableEq ℚ]
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208)
    (hsquare : IsSquare
      (BillingMahlerField.ofCoords (xi - 24) 18 0)) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = mordellPoint xi eta hcurve := by
  rcases hsquare with ⟨gamma, hgamma⟩
  obtain ⟨a, b, c, hcoords⟩ := BillingMahlerField.exists_ofCoords gamma
  have hsquareCoords :
      BillingMahlerField.ofCoords (xi - 24) 18 0 =
        BillingMahlerField.ofCoords a b c ^ 2 := by
    rw [← hcoords]
    simpa [pow_two] using hgamma
  rw [BillingMahlerField.ofCoords_sq] at hsquareCoords
  have hzero := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (0 : Fin 3)) hsquareCoords
  have hone := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (1 : Fin 3)) hsquareCoords
  have htwo := congrArg
    (fun q : K ↦ BillingMahlerField.basis.repr q (2 : Fin 3)) hsquareCoords
  simp only [BillingMahlerField.basis_repr_ofCoords_zero] at hzero
  simp only [BillingMahlerField.basis_repr_ofCoords_one] at hone
  simp only [BillingMahlerField.basis_repr_ofCoords_two] at htwo
  have hezero :
      a ^ 2 + 4 * b * c + 8 * c ^ 2 - xi + 24 = 0 := by
    linarith
  have heone :
      2 * a * b - 8 * b * c - 14 * c ^ 2 - 18 = 0 := by
    linarith
  have hetwo :
      b ^ 2 + 2 * a * c + 8 * b * c + 12 * c ^ 2 = 0 := by
    linarith
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    norm_num at hetwo
    have hb : b = 0 := hetwo
    subst b
    norm_num at heone
  have hg :
      b ^ 3 + 8 * b ^ 2 * c + 20 * b * c ^ 2 + 14 * c ^ 3 + 18 * c = 0 := by
    linear_combination b * hetwo - c * heone
  let U : ℚ := -48 * c - 18 * b
  let M : ℚ := a * c - 4 * b * c - b ^ 2 - 4 * c ^ 2
  let N : ℚ := 48 * a * c + 96 * b * c + 60 * c ^ 2 +
    18 * a * b + 24 * b ^ 2
  let u : ℚ := U / c
  let m : ℚ := M / c
  let n : ℚ := N / c
  have hscaled₂ : -M ^ 2 + 2 * U * c + xi * c ^ 2 = 0 := by
    dsimp [U, M]
    linear_combination
      -(c ^ 2) * hezero + c * (b + 4 * c) * heone +
        4 * c ^ 2 * hetwo - b * hg
  have hscaled₁ :
      -432 * c ^ 2 - 2 * M * N - U ^ 2 - 2 * xi * U * c = 0 := by
    dsimp [U, M, N]
    linear_combination
      (-12 * c * (3 * b + 8 * c)) * hezero +
        (6 * (3 * b ^ 2 + 16 * b * c + 28 * c ^ 2)) * heone +
        132 * c ^ 2 * hetwo + 48 * (b + 3 * c) * hg
  have hscaled₀ : 8208 * c ^ 2 - N ^ 2 + xi * U ^ 2 = 0 := by
    dsimp [U, N]
    linear_combination
      (-36 * (3 * b + 8 * c) ^ 2) * hezero +
        (-72 * (6 * b ^ 2 + 40 * b * c + 79 * c ^ 2)) * heone +
        (-2880 * c ^ 2) * hetwo - 144 * (4 * b + 15 * c) * hg
  have hcoef₂ : -m ^ 2 + 2 * u + xi = 0 := by
    dsimp [m, u]
    field_simp [hc]
    convert hscaled₂ using 1 <;> ring
  have hcoef₁ : -432 - 2 * m * n - u ^ 2 - 2 * xi * u = 0 := by
    dsimp [m, n, u]
    field_simp [hc]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled₁
  have hcoef₀ : 8208 - n ^ 2 + xi * u ^ 2 = 0 := by
    dsimp [n, u]
    field_simp [hc]
    simpa using hscaled₀
  have hlineAtXi :
      xi ^ 3 - 432 * xi + 8208 - (m * xi + n) ^ 2 = 0 := by
    linear_combination xi ^ 2 * hcoef₂ + xi * hcoef₁ + hcoef₀
  have hlineSq : (m * xi + n) ^ 2 = eta ^ 2 := by
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hlineSq with hsign | hsign
  · apply exists_mordell_half_of_line hcurve
      (u := u) (m := -m) (n := -n)
    · simpa using hcoef₂
    · simpa using hcoef₁
    · simpa using hcoef₀
    · linear_combination -hsign
  · exact exists_mordell_half_of_line hcurve hcoef₂ hcoef₁ hcoef₀ hsign

/-! ## Explicit division-polynomial certificates at two -/

def divS {R : Type*} [CommRing R] (x : R) : R :=
  4 * x ^ 3 - 4 * x ^ 2 + 1

def divP {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 4 - 4 * x ^ 3 + 3 * x - 1

def divQ {R : Type*} [CommRing R] (x : R) : R :=
  2 * x ^ 6 - 4 * x ^ 5 + 10 * x ^ 3 - 10 * x ^ 2 + 4 * x - 1

def divR {R : Type*} [CommRing R] (x : R) : R :=
  divS x ^ 2 * divQ x - divP x ^ 3

def divPhi5 {R : Type*} [CommRing R] (x : R) : R :=
  x * divR x ^ 2 -
    divP x * divS x * divQ x * (divR x - divQ x ^ 2)

def divPhi2 {R : Type*} [CommRing R] (x : R) : R :=
  x ^ 4 - 2 * x + 1

def divSH {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 - 4 * a ^ 2 * b + b ^ 3

def divPH {R : Type*} [CommRing R] (a b : R) : R :=
  3 * a ^ 4 - 4 * a ^ 3 * b + 3 * a * b ^ 3 - b ^ 4

def divQH {R : Type*} [CommRing R] (a b : R) : R :=
  2 * a ^ 6 - 4 * a ^ 5 * b + 10 * a ^ 3 * b ^ 3 -
    10 * a ^ 2 * b ^ 4 + 4 * a * b ^ 5 - b ^ 6

def divRH {R : Type*} [CommRing R] (a b : R) : R :=
  divSH a b ^ 2 * divQH a b - divPH a b ^ 3

def divPhi5H {R : Type*} [CommRing R] (a b : R) : R :=
  a * divRH a b ^ 2 -
    divPH a b * divSH a b * divQH a b *
      (divRH a b - divQH a b ^ 2)

private theorem divRH_dehom (a b : ℚ) (hb : b ≠ 0) :
    divRH a b = b ^ 12 * divR (a / b) := by
  unfold divRH divSH divPH divQH divR divS divP divQ
  field_simp [hb]
  <;> ring

private theorem divPhi5H_dehom (a b : ℚ) (hb : b ≠ 0) :
    divPhi5H a b = b ^ 25 * divPhi5 (a / b) := by
  unfold divPhi5H divRH divSH divPH divQH
    divPhi5 divR divS divP divQ
  field_simp [hb]
  <;> ring

private theorem mod_two_five_certificate :
    ∀ a b : ZMod 2, b ≠ 0 →
      divRH a b = 0 ∧ divPhi5H a b = 1 := by
  decide

theorem minimalCurve_PsiSq_five_eval (x : ℚ) :
    (minimalCurve.ΨSq (5 : ℤ)).eval x = divR x ^ 2 := by
  change (minimalCurve.ΨSq ((5 : ℕ) : ℤ)).eval x = divR x ^ 2
  rw [minimalCurve.ΨSq_ofNat 5]
  simp only [show ¬Even (5 : ℕ) by decide, if_false, mul_one,
    Polynomial.eval_pow]
  rw [show 5 = 2 * (0 + 2) + 1 by norm_num,
    minimalCurve.preΨ'_odd 0]
  simp [divR, divS, divP, divQ, minimalCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem minimalCurve_Phi_five_eval (x : ℚ) :
    (minimalCurve.Φ (5 : ℤ)).eval x = divPhi5 x := by
  rw [show (5 : ℤ) = ((4 : ℕ) + 1 : ℤ) by norm_num,
    minimalCurve.Φ_ofNat 4]
  simp only [Nat.reduceAdd, show Even (4 : ℕ) by decide, if_pos, mul_one]
  rw [show 6 = 2 * (0 + 3) by norm_num,
    minimalCurve.preΨ'_even 0]
  rw [show 5 = 2 * (0 + 2) + 1 by norm_num,
    minimalCurve.preΨ'_odd 0]
  simp [divPhi5, divR, divS, divP, divQ, minimalCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem minimalCurve_PsiSq_two_eval (x : ℚ) :
    (minimalCurve.ΨSq (2 : ℤ)).eval x = divS x := by
  rw [minimalCurve.ΨSq_two]
  simp [divS, minimalCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

theorem minimalCurve_Phi_two_eval (x : ℚ) :
    (minimalCurve.Φ (2 : ℤ)).eval x = divPhi2 x := by
  rw [minimalCurve.Φ_two]
  simp [divPhi2, minimalCurve, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private theorem v2_add_eq_left_of_lt
    {a b : ℚ} (ha : a ≠ 0)
    (h : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hz
    have hba : b = -a := by linarith
    rw [hba, padicValRat.neg] at h
    exact (lt_irrefl _ h)
  exact padicValRat.add_eq_of_lt hab ha hb h

private theorem v2_list_sum_zero_or_gt
    (a : ℚ) (L : List ℚ)
    (hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q) :
    L.sum = 0 ∨ padicValRat 2 a < padicValRat 2 L.sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
      have hq : padicValRat 2 a < padicValRat 2 q := hL q (by simp)
      have htail : ∀ r ∈ L, padicValRat 2 a < padicValRat 2 r := by
        intro r hr
        exact hL r (by simp [hr])
      rcases ih htail with hzero | hgt
      · rw [List.sum_cons, hzero, add_zero]
        by_cases hq0 : q = 0
        · exact Or.inl hq0
        · exact Or.inr hq
      · rw [List.sum_cons]
        by_cases hsum : q + L.sum = 0
        · exact Or.inl hsum
        · exact Or.inr (padicValRat.lt_add_of_lt hsum hq hgt)

private theorem v2_add_list_sum_eq
    {a : ℚ} (ha : a ≠ 0) (L : List ℚ)
    (hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q) :
    padicValRat 2 (a + L.sum) = padicValRat 2 a := by
  rcases v2_list_sum_zero_or_gt a L hL with hzero | hgt
  · simp [hzero]
  · exact v2_add_eq_left_of_lt ha hgt

private theorem v2_two : padicValRat 2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by norm_num)

private theorem v2_three : padicValRat 2 (3 : ℚ) = 0 := by
  change padicValRat 2 ((3 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (p := 2) (n := 3) (by norm_num)

private theorem v2_five : padicValRat 2 (5 : ℚ) = 0 := by
  change padicValRat 2 ((5 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd (p := 2) (n := 5) (by norm_num)

private theorem v2_four : padicValRat 2 (4 : ℚ) = 2 := by
  calc
    padicValRat 2 (4 : ℚ) = padicValRat 2 ((2 : ℚ) ^ 2) := by norm_num
    _ = (2 : ℤ) * padicValRat 2 (2 : ℚ) :=
      padicValRat.pow _
    _ = 2 := by rw [v2_two]; norm_num

private theorem v2_ten : padicValRat 2 (10 : ℚ) = 1 := by
  calc
    padicValRat 2 (10 : ℚ) = padicValRat 2 ((2 : ℚ) * 5) := by norm_num
    _ = padicValRat 2 (2 : ℚ) + padicValRat 2 (5 : ℚ) :=
      padicValRat.mul (by norm_num) (by norm_num)
    _ = 1 := by rw [v2_two, v2_five]; norm_num

private theorem divS_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divS x ≠ 0 ∧ padicValRat 2 (divS x) = 3 * padicValRat 2 x + 2 := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 4 * x ^ 3
  let L : List ℚ := [-4 * x ^ 2, 1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hx0)
  have hva : padicValRat 2 a = 3 * padicValRat 2 x + 2 := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
      padicValRat.pow _, v2_four]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 2 hx0),
        padicValRat.pow _, v2_four, hva]
      omega
    · rw [padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divS x := by
    simp [a, L, divS]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divP_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divP x ≠ 0 ∧ padicValRat 2 (divP x) = 4 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 3 * x ^ 4
  let L : List ℚ := [-4 * x ^ 3, 3 * x, -1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0)
  have hva : padicValRat 2 a = 4 * padicValRat 2 x := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 4 hx0),
      padicValRat.pow _, v2_three]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
        padicValRat.pow _, v2_four, hva]
      omega
    · rw [padicValRat.mul (by norm_num) hx0, v2_three, hva]
      omega
    · rw [padicValRat.neg, padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divP x := by
    simp [a, L, divP]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divQ_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divQ x ≠ 0 ∧ padicValRat 2 (divQ x) = 6 * padicValRat 2 x + 1 := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := 2 * x ^ 6
  let L : List ℚ :=
    [-4 * x ^ 5, 10 * x ^ 3, -10 * x ^ 2, 4 * x, -1]
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 6 hx0)
  have hva : padicValRat 2 a = 6 * padicValRat 2 x + 1 := by
    dsimp [a]
    rw [padicValRat.mul (by norm_num) (pow_ne_zero 6 hx0),
      padicValRat.pow _, v2_two]
    ring
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 5 hx0),
        padicValRat.pow _, v2_four, hva]
      omega
    · rw [padicValRat.mul (by norm_num) (pow_ne_zero 3 hx0),
        padicValRat.pow _, v2_ten, hva]
      omega
    · rw [padicValRat.neg,
        padicValRat.mul (by norm_num) (pow_ne_zero 2 hx0),
        padicValRat.pow _, v2_ten, hva]
      omega
    · rw [padicValRat.mul (by norm_num) hx0, v2_four, hva]
      omega
    · rw [padicValRat.neg, padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divQ x := by
    simp [a, L, divQ]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divR_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divR x ≠ 0 ∧ padicValRat 2 (divR x) = 12 * padicValRat 2 x := by
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hP0, hP⟩ := divP_v2_of_neg hx
  obtain ⟨hQ0, hQ⟩ := divQ_v2_of_neg hx
  have hleft0 : divS x ^ 2 * divQ x ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hS0) hQ0
  have hright0 : -(divP x ^ 3) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 3 hP0)
  have hleft :
      padicValRat 2 (divS x ^ 2 * divQ x) =
        12 * padicValRat 2 x + 5 := by
    rw [padicValRat.mul (pow_ne_zero 2 hS0) hQ0,
      padicValRat.pow _, hS, hQ]
    ring
  have hright :
      padicValRat 2 (-(divP x ^ 3)) = 12 * padicValRat 2 x := by
    rw [padicValRat.neg, padicValRat.pow _, hP]
    ring
  have hval : padicValRat 2 (divS x ^ 2 * divQ x + -(divP x ^ 3)) =
      padicValRat 2 (-(divP x ^ 3)) := by
    rw [add_comm]
    apply v2_add_eq_left_of_lt hright0
    rw [hleft, hright]
    omega
  have hform : divS x ^ 2 * divQ x + -(divP x ^ 3) = divR x := by
    simp [divR, sub_eq_add_neg]
  rw [hform, hright] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divPhi5_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divPhi5 x ≠ 0 ∧
      padicValRat 2 (divPhi5 x) = 25 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hP0, hP⟩ := divP_v2_of_neg hx
  obtain ⟨hQ0, hQ⟩ := divQ_v2_of_neg hx
  obtain ⟨hR0, hR⟩ := divR_v2_of_neg hx
  have hQsq :
      padicValRat 2 (divQ x ^ 2) = 12 * padicValRat 2 x + 2 := by
    rw [padicValRat.pow _, hQ]
    ring
  have hdiff0 : divR x - divQ x ^ 2 ≠ 0 := by
    intro hzero
    have heq : divR x = divQ x ^ 2 := sub_eq_zero.mp hzero
    have hvals := congrArg (padicValRat 2) heq
    rw [hR, hQsq] at hvals
    omega
  have hdiff :
      padicValRat 2 (divR x - divQ x ^ 2) =
        12 * padicValRat 2 x := by
    rw [sub_eq_add_neg]
    rw [v2_add_eq_left_of_lt hR0, hR]
    rw [padicValRat.neg, hQsq, hR]
    omega
  have hfirst0 : x * divR x ^ 2 ≠ 0 :=
    mul_ne_zero hx0 (pow_ne_zero 2 hR0)
  have hsecond0 :
      -(divP x * divS x * divQ x * (divR x - divQ x ^ 2)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hP0 hS0) hQ0) hdiff0)
  have hfirst :
      padicValRat 2 (x * divR x ^ 2) = 25 * padicValRat 2 x := by
    rw [padicValRat.mul hx0 (pow_ne_zero 2 hR0),
      padicValRat.pow _, hR]
    ring
  have hsecond : padicValRat 2
      (-(divP x * divS x * divQ x * (divR x - divQ x ^ 2))) =
        25 * padicValRat 2 x + 3 := by
    rw [padicValRat.neg,
      padicValRat.mul (mul_ne_zero (mul_ne_zero hP0 hS0) hQ0) hdiff0,
      padicValRat.mul (mul_ne_zero hP0 hS0) hQ0,
      padicValRat.mul hP0 hS0, hP, hS, hQ, hdiff]
    ring
  have hval := v2_add_eq_left_of_lt hfirst0 (by
    rw [hfirst, hsecond]
    omega : padicValRat 2 (x * divR x ^ 2) <
      padicValRat 2
        (-(divP x * divS x * divQ x * (divR x - divQ x ^ 2))))
  have hform :
      x * divR x ^ 2 +
        -(divP x * divS x * divQ x * (divR x - divQ x ^ 2)) =
          divPhi5 x := by
    simp [divPhi5, sub_eq_add_neg]
  rw [hform, hfirst] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem divPhi2_v2_of_neg {x : ℚ}
    (hx : padicValRat 2 x < 0) :
    divPhi2 x ≠ 0 ∧
      padicValRat 2 (divPhi2 x) = 4 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
  let a : ℚ := x ^ 4
  let L : List ℚ := [-2 * x, 1]
  have ha : a ≠ 0 := pow_ne_zero 4 hx0
  have hva : padicValRat 2 a = 4 * padicValRat 2 x := by
    dsimp [a]
    rw [padicValRat.pow _]
    norm_num
  have hL : ∀ q ∈ L, padicValRat 2 a < padicValRat 2 q := by
    intro q hq
    simp [L] at hq
    rcases hq with rfl | rfl
    · rw [padicValRat.neg, padicValRat.mul (by norm_num) hx0,
        v2_two, hva]
      omega
    · rw [padicValRat.one, hva]
      omega
  have hval := v2_add_list_sum_eq ha L hL
  have hform : a + L.sum = divPhi2 x := by
    simp [a, L, divPhi2]
    ring
  rw [hform, hva] at hval
  refine ⟨?_, hval⟩
  intro hzero
  rw [hzero, padicValRat.zero] at hval
  omega

private theorem rat_den_not_even_of_v2_nonneg
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ¬ 2 ∣ x.den := by
  intro hden
  have hcop : Nat.Coprime x.num.natAbs 2 :=
    Nat.Coprime.of_dvd_right hden x.reduced
  have hnumAbs : ¬ 2 ∣ x.num.natAbs :=
    Nat.prime_two.coprime_iff_not_dvd.mp hcop.symm
  have hnum : ¬ (2 : ℤ) ∣ x.num := by
    intro hdiv
    exact hnumAbs (Int.natCast_dvd.mp hdiv)
  have hnumVal : padicValInt 2 x.num = 0 :=
    padicValInt.eq_zero_of_not_dvd hnum
  have hdenVal : 1 ≤ padicValNat 2 x.den :=
    one_le_padicValNat_of_dvd x.den_nz hden
  rw [padicValRat_def, hnumVal] at hx
  omega

private theorem rat_den_v2_eq_zero
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    padicValRat 2 (x.den : ℚ) = 0 := by
  change padicValRat 2 ((x.den : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd
    (rat_den_not_even_of_v2_nonneg x hx)

private theorem divR_num_den_formula (x : ℚ) :
    divR x =
      (divRH x.num (x.den : ℤ) : ℤ) /
        (x.den : ℚ) ^ 12 := by
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divRH_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  have hcast :
      ((divRH x.num (x.den : ℤ) : ℤ) : ℚ) =
        divRH (x.num : ℚ) (x.den : ℚ) := by
    norm_num [divRH, divSH, divPH, divQH]
  calc
    divR x = divR ((x.num : ℚ) / (x.den : ℚ)) := by rw [← hxrepr]
    _ = divRH (x.num : ℚ) (x.den : ℚ) / (x.den : ℚ) ^ 12 := by
      rw [hdehom]
      field_simp
    _ = (divRH x.num (x.den : ℤ) : ℤ) / (x.den : ℚ) ^ 12 := by
      rw [hcast]

private theorem divPhi5_num_den_formula (x : ℚ) :
    divPhi5 x =
      (divPhi5H x.num (x.den : ℤ) : ℤ) /
        (x.den : ℚ) ^ 25 := by
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divPhi5H_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  have hcast :
      ((divPhi5H x.num (x.den : ℤ) : ℤ) : ℚ) =
        divPhi5H (x.num : ℚ) (x.den : ℚ) := by
    norm_num [divPhi5H, divRH, divSH, divPH, divQH]
  calc
    divPhi5 x = divPhi5 ((x.num : ℚ) / (x.den : ℚ)) := by rw [← hxrepr]
    _ = divPhi5H (x.num : ℚ) (x.den : ℚ) / (x.den : ℚ) ^ 25 := by
      rw [hdehom]
      field_simp
    _ = (divPhi5H x.num (x.den : ℤ) : ℤ) / (x.den : ℚ) ^ 25 := by
      rw [hcast]

private theorem integral_five_homogeneous_certificate
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    (2 : ℤ) ∣ (divRH x.num (x.den : ℤ) : ℤ) ∧
      ¬ (2 : ℤ) ∣ (divPhi5H x.num (x.den : ℤ) : ℤ) := by
  have hden : ¬ 2 ∣ x.den := rat_den_not_even_of_v2_nonneg x hx
  have hb : ((x.den : ZMod 2) : ZMod 2) ≠ 0 := by
    have hbInt : (((x.den : ℤ) : ZMod 2)) ≠ 0 := by
      intro hb0
      apply hden
      exact Int.natCast_dvd.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) 2).mp hb0)
    simpa using hbInt
  have hcert := mod_two_five_certificate (x.num : ZMod 2) (x.den : ZMod 2) hb
  have hRmod :
      ((divRH x.num (x.den : ℤ) : ℤ) : ZMod 2) = 0 := by
    simpa [divRH, divSH, divPH, divQH] using hcert.1
  have hPhimod :
      ((divPhi5H x.num (x.den : ℤ) : ℤ) : ZMod 2) = 1 := by
    simpa [divPhi5H, divRH, divSH, divPH, divQH] using hcert.2
  constructor
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hRmod
  · intro hdiv
    have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdiv
    rw [hPhimod] at hzero
    norm_num at hzero

private theorem divR_zero_or_v2_pos_of_nonneg {x : ℚ}
    (hx : 0 ≤ padicValRat 2 x) :
    divR x = 0 ∨
      divR x ≠ 0 ∧ 1 ≤ padicValRat 2 (divR x) := by
  by_cases hR0 : divR x = 0
  · exact Or.inl hR0
  · right
    refine ⟨hR0, ?_⟩
    let A : ℤ := divRH x.num (x.den : ℤ)
    have hAdiv : (2 : ℤ) ∣ A :=
      (integral_five_homogeneous_certificate x hx).1
    have hA0 : A ≠ 0 := by
      intro hzero
      apply hR0
      rw [divR_num_den_formula, show (divRH x.num (x.den : ℤ) : ℤ) = A by rfl,
        hzero]
      simp
    have hAvalNat : 1 ≤ padicValNat 2 A.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hA0)
        (Int.natCast_dvd.mp hAdiv)
    have hAval : 1 ≤ padicValRat 2 (A : ℚ) := by
      rw [padicValRat.of_int]
      exact_mod_cast hAvalNat
    have hdenVal := rat_den_v2_eq_zero x hx
    rw [divR_num_den_formula,
      show (divRH x.num (x.den : ℤ) : ℤ) = A by rfl,
      padicValRat.div (Int.cast_ne_zero.mpr hA0)
        (pow_ne_zero 12 (by positivity)),
      padicValRat.pow _, hdenVal]
    omega

private theorem divPhi5_v2_of_nonneg {x : ℚ}
    (hx : 0 ≤ padicValRat 2 x) :
    divPhi5 x ≠ 0 ∧ padicValRat 2 (divPhi5 x) = 0 := by
  let A : ℤ := divPhi5H x.num (x.den : ℤ)
  have hAnotdiv : ¬ (2 : ℤ) ∣ A :=
    (integral_five_homogeneous_certificate x hx).2
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hAnotdiv
    simp [hzero]
  have hAval : padicValRat 2 (A : ℚ) = 0 := by
    rw [padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hAnotdiv
  have hdenVal := rat_den_v2_eq_zero x hx
  have hformula := divPhi5_num_den_formula x
  have hPhi0 : divPhi5 x ≠ 0 := by
    rw [hformula, show (divPhi5H x.num (x.den : ℤ) : ℤ) = A by rfl]
    exact div_ne_zero (Int.cast_ne_zero.mpr hA0) (pow_ne_zero 25 (by positivity))
  refine ⟨hPhi0, ?_⟩
  rw [hformula, show (divPhi5H x.num (x.den : ℤ) : ℤ) = A by rfl,
    padicValRat.div (Int.cast_ne_zero.mpr hA0)
      (pow_ne_zero 25 (by positivity)),
    padicValRat.pow _, hAval, hdenVal]
  norm_num

private theorem psi_ne_zero_of_charZero
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hpsi2ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
          (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hpsi2deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsine : ∀ (n : ℕ), n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hpsi2ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsideg : ∀ (n : ℕ), n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree ≤ 0 + 1 :=
          Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add (Polynomial.natDegree_C _).le hpsi2deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hmk :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hmk (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine n (by intro h; exact hm (by simp [h])))
      (hPsideg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsine _ (Nat.succ_ne_zero n))
      (hPsideg _ (Nat.succ_ne_zero n))

section

noncomputable local instance : DecidableEq ℚ := Classical.decEq ℚ

private theorem minimal_five_xrep_same
    {x y : ℚ} (h : MinimalCurveBase.Nonsingular x y) :
    KeystoneLadder.SameP1Vec
      (((5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint)).xRep)
      (KeystoneLadder.xPair minimalCurve (5 : ℤ) x) := by
  exact KeystoneLadder.xRep_nsmul_same_xPair minimalCurve
    (by norm_num) (psi_ne_zero_of_charZero minimalCurve)
    (WeierstrassCurve.Ψ₃_ne_zero minimalCurve (by norm_num)) (n := 5) h

private theorem minimal_five_cross_multiplication
    {x y x5 y5 : ℚ}
    {h : MinimalCurveBase.Nonsingular x y}
    {h5 : MinimalCurveBase.Nonsingular x5 y5}
    (heq : (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
      WeierstrassCurve.Affine.Point.some x5 y5 h5) :
    x5 * divR x ^ 2 = divPhi5 x := by
  have hsame := minimal_five_xrep_same h
  rw [heq] at hsame
  rcases hsame with ⟨c, hc, hvec⟩
  have hzero := congrArg (fun v : Fin 2 → ℚ ↦ v 0) hvec
  have hone := congrArg (fun v : Fin 2 → ℚ ↦ v 1) hvec
  simp [KeystoneLadder.xPair, Pi.smul_apply,
    minimalCurve_Phi_five_eval, minimalCurve_PsiSq_five_eval] at hzero hone
  calc
    x5 * divR x ^ 2 = x5 * c := by rw [hone]
    _ = c * x5 := mul_comm _ _
    _ = divPhi5 x := hzero.symm

def InFormal2 : MinimalPoint → Prop
  | WeierstrassCurve.Affine.Point.zero => True
  | WeierstrassCurve.Affine.Point.some x _ _ => padicValRat 2 x < 0

@[simp] theorem inFormal2_zero : InFormal2 (0 : MinimalPoint) := by
  rw [WeierstrassCurve.Affine.Point.zero_def]
  change True
  trivial

@[simp] theorem inFormal2_some (x y : ℚ)
    (h : MinimalCurveBase.Nonsingular x y) :
    InFormal2 (WeierstrassCurve.Affine.Point.some x y h) ↔
      padicValRat 2 x < 0 := by
  rfl

theorem five_nsmul_inFormal2 (P : MinimalPoint) :
    InFormal2 ((5 : ℕ) • P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← WeierstrassCurve.Affine.Point.zero_def]
    simp
  · by_cases hx : padicValRat 2 x < 0
    · obtain ⟨hR0, hR⟩ := divR_v2_of_neg hx
      obtain ⟨hPhi0, hPhi⟩ := divPhi5_v2_of_neg hx
      cases heq : (5 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
      | zero => change True; trivial
      | some x5 y5 h5 =>
          rw [inFormal2_some]
          have hcross := minimal_five_cross_multiplication heq
          have hx50 : x5 ≠ 0 := by
            intro hx50
            rw [hx50, zero_mul] at hcross
            exact hPhi0 hcross.symm
          have hval := congrArg (padicValRat 2) hcross
          rw [padicValRat.mul hx50 (pow_ne_zero 2 hR0),
            padicValRat.pow _, hR, hPhi] at hval
          omega
    · have hxnonneg : 0 ≤ padicValRat 2 x := by omega
      obtain ⟨hPhi0, hPhi⟩ := divPhi5_v2_of_nonneg hxnonneg
      rcases divR_zero_or_v2_pos_of_nonneg hxnonneg with hRzero | ⟨hR0, hR⟩
      · cases heq : (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
        | zero => change True; trivial
        | some x5 y5 h5 =>
            exfalso
            have hcross := minimal_five_cross_multiplication heq
            rw [hRzero] at hcross
            norm_num at hcross
            exact hPhi0 hcross.symm
      · cases heq : (5 : ℕ) •
            (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
        | zero => change True; trivial
        | some x5 y5 h5 =>
            rw [inFormal2_some]
            have hcross := minimal_five_cross_multiplication heq
            have hx50 : x5 ≠ 0 := by
              intro hx50
              rw [hx50, zero_mul] at hcross
              exact hPhi0 hcross.symm
            have hval := congrArg (padicValRat 2) hcross
            rw [padicValRat.mul hx50 (pow_ne_zero 2 hR0),
              padicValRat.pow _, hPhi] at hval
            omega

private theorem minimal_two_xrep_same
    {x y : ℚ} (h : MinimalCurveBase.Nonsingular x y) :
    KeystoneLadder.SameP1Vec
      (((2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint)).xRep)
      (KeystoneLadder.xPair minimalCurve (2 : ℤ) x) := by
  exact KeystoneLadder.xRep_nsmul_same_xPair minimalCurve
    (by norm_num) (psi_ne_zero_of_charZero minimalCurve)
    (WeierstrassCurve.Ψ₃_ne_zero minimalCurve (by norm_num)) (n := 2) h

private theorem minimal_two_cross_multiplication
    {x y x2 y2 : ℚ}
    {h : MinimalCurveBase.Nonsingular x y}
    {h2 : MinimalCurveBase.Nonsingular x2 y2}
    (heq : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
      WeierstrassCurve.Affine.Point.some x2 y2 h2) :
    x2 * divS x = divPhi2 x := by
  have hsame := minimal_two_xrep_same h
  rw [heq] at hsame
  rcases hsame with ⟨c, hc, hvec⟩
  have hzero := congrArg (fun v : Fin 2 → ℚ ↦ v 0) hvec
  have hone := congrArg (fun v : Fin 2 → ℚ ↦ v 1) hvec
  simp [KeystoneLadder.xPair, Pi.smul_apply] at hzero hone
  have hzero' : divPhi2 x = c * x2 := by
    calc
      divPhi2 x = x ^ 4 - minimalCurve.b₄ * x ^ 2 -
          2 * minimalCurve.b₆ * x - minimalCurve.b₈ := by
        simp [divPhi2, minimalCurve, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      _ = c * x2 := hzero
  have hone' : divS x = c := by
    calc
      divS x = minimalCurve.Ψ₂Sq.eval x :=
        (by simpa using (minimalCurve_PsiSq_two_eval x).symm)
      _ = c := hone
  calc
    x2 * divS x = x2 * c := by rw [hone']
    _ = c * x2 := mul_comm _ _
    _ = divPhi2 x := hzero'.symm

private theorem double_formal_coordinates
    {x y : ℚ} {h : MinimalCurveBase.Nonsingular x y}
    (hx : padicValRat 2 x < 0) :
    ∃ x2 y2 : ℚ, ∃ h2 : MinimalCurveBase.Nonsingular x2 y2,
      (2 : ℕ) •
          (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) =
        WeierstrassCurve.Affine.Point.some x2 y2 h2 ∧
      padicValRat 2 x2 = padicValRat 2 x - 2 := by
  obtain ⟨hS0, hS⟩ := divS_v2_of_neg hx
  obtain ⟨hPhi0, hPhi⟩ := divPhi2_v2_of_neg hx
  cases heq : (2 : ℕ) •
      (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) with
  | zero =>
      have hsame := minimal_two_xrep_same h
      rw [heq] at hsame
      have hsecond :=
        KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty (by
          simpa only [← WeierstrassCurve.Affine.Point.zero_def,
            WeierstrassCurve.Affine.Point.xRep_zero] using hsame)
      have hSzero : divS x = 0 := by
        have hraw : minimalCurve.Ψ₂Sq.eval x = 0 := by
          simpa [KeystoneLadder.xPair] using hsecond
        rw [← minimalCurve_PsiSq_two_eval]
        simpa using hraw
      exact (hS0 hSzero).elim
  | some x2 y2 h2 =>
      refine ⟨x2, y2, h2, ?_, ?_⟩
      · simpa only using heq
      · have hcross := minimal_two_cross_multiplication
          (x := x) (y := y) (x2 := x2) (y2 := y2) (by
            simpa only using heq)
        have hx20 : x2 ≠ 0 := by
          intro hx20
          rw [hx20, zero_mul] at hcross
          exact hPhi0 hcross.symm
        have hval := congrArg (padicValRat 2) hcross
        rw [padicValRat.mul hx20 hS0, hS, hPhi] at hval
        omega

def FormalVal (P : MinimalPoint) (k : ℤ) : Prop :=
  ∃ x y : ℚ, ∃ h : MinimalCurveBase.Nonsingular x y,
    P = WeierstrassCurve.Affine.Point.some x y h ∧
      padicValRat 2 x = k ∧ k < 0

private theorem formalVal_two {P : MinimalPoint} {k : ℤ}
    (hP : FormalVal P k) : FormalVal ((2 : ℕ) • P) (k - 2) := by
  obtain ⟨x, y, h, rfl, hx, hk⟩ := hP
  obtain ⟨x2, y2, h2, hdouble, hx2⟩ :=
    double_formal_coordinates (hx ▸ hk)
  refine ⟨x2, y2, h2, hdouble, ?_, by omega⟩
  omega

private theorem formalVal_two_pow {P : MinimalPoint} {k : ℤ}
    (hP : FormalVal P k) (n : ℕ) :
    FormalVal ((2 ^ n : ℕ) • P) (k - 2 * (n : ℤ)) := by
  induction n with
  | zero => simpa using hP
  | succ n ih =>
      have htwo := formalVal_two ih
      convert htwo using 1
      · calc
          (2 ^ (n + 1) : ℕ) • P = (2 ^ n * 2 : ℕ) • P := by
            rw [pow_succ]
          _ = (2 : ℕ) • ((2 ^ n : ℕ) • P) :=
            mul_nsmul P (2 ^ n) 2
      · push_cast
        ring

def InfinitelyTwoDivisible (P : MinimalPoint) : Prop :=
  ∀ n : ℕ, ∃ Q : MinimalPoint, (2 ^ n : ℕ) • Q = P

theorem five_nsmul_eq_zero_of_infinitelyTwoDivisible
    {P : MinimalPoint} (hdiv : InfinitelyTwoDivisible P) :
    (5 : ℕ) • P = 0 := by
  by_contra hne
  let R : MinimalPoint := (5 : ℕ) • P
  have hRne : R ≠ 0 := hne
  cases hReq : R with
  | zero =>
      apply hRne
      simpa [WeierstrassCurve.Affine.Point.zero_def] using hReq
  | some xr yr hr =>
      let n : ℕ := (padicValRat 2 xr).natAbs + 1
      obtain ⟨Q, hQ⟩ := hdiv n
      let S : MinimalPoint := (5 : ℕ) • Q
      have hrel : (2 ^ n : ℕ) • S = R := by
        dsimp [S, R]
        calc
          (2 ^ n : ℕ) • ((5 : ℕ) • Q) = (5 * 2 ^ n : ℕ) • Q :=
            (mul_nsmul Q 5 (2 ^ n)).symm
          _ = (2 ^ n * 5 : ℕ) • Q := by rw [Nat.mul_comm]
          _ = (5 : ℕ) • ((2 ^ n : ℕ) • Q) :=
            mul_nsmul Q (2 ^ n) 5
          _ = (5 : ℕ) • P := by rw [hQ]
      have hformal : InFormal2 S := five_nsmul_inFormal2 Q
      cases hSeq : S with
      | zero =>
          have hSzero : S = (0 : MinimalPoint) := by
            simpa [WeierstrassCurve.Affine.Point.zero_def] using hSeq
          apply hRne
          rw [← hrel, hSzero]
          simp
      | some xs ys hs =>
          have hxs : padicValRat 2 xs < 0 := by
            rw [hSeq] at hformal
            exact hformal
          have hFV : FormalVal S (padicValRat 2 xs) :=
            ⟨xs, ys, hs, hSeq, rfl, hxs⟩
          have hiter := formalVal_two_pow hFV n
          rw [hrel] at hiter
          obtain ⟨xt, yt, ht, hpoint, hval, _⟩ := hiter
          have hxeq : xr = xt := by
            have heqPoints :
                (WeierstrassCurve.Affine.Point.some xr yr hr : MinimalPoint) =
                  WeierstrassCurve.Affine.Point.some xt yt ht :=
              hReq.symm.trans hpoint
            rw [WeierstrassCurve.Affine.Point.some.injEq] at heqPoints
            exact heqPoints.1
          rw [← hxeq] at hval
          dsimp [n] at hval
          push_cast at hval
          by_cases hV : 0 ≤ padicValRat 2 xr
          · rw [abs_of_nonneg hV] at hval
            omega
          · have hVneg : padicValRat 2 xr < 0 := lt_of_not_ge hV
            rw [abs_of_neg hVneg] at hval
            omega

def divQ10 {R : Type*} [CommRing R] (x : R) : R :=
  5 * x ^ 10 - 15 * x ^ 9 + x ^ 8 + 96 * x ^ 7 -
    189 * x ^ 6 + 171 * x ^ 5 - 84 * x ^ 4 + 10 * x ^ 3 +
    25 * x ^ 2 - 20 * x + 5

def divQ10H {R : Type*} [CommRing R] (a b : R) : R :=
  5 * a ^ 10 - 15 * a ^ 9 * b + a ^ 8 * b ^ 2 +
    96 * a ^ 7 * b ^ 3 - 189 * a ^ 6 * b ^ 4 +
    171 * a ^ 5 * b ^ 5 - 84 * a ^ 4 * b ^ 6 +
    10 * a ^ 3 * b ^ 7 + 25 * a ^ 2 * b ^ 8 -
    20 * a * b ^ 9 + 5 * b ^ 10

private theorem divQ10H_dehom (a b : ℚ) (hb : b ≠ 0) :
    divQ10H a b = b ^ 10 * divQ10 (a / b) := by
  unfold divQ10H divQ10
  field_simp [hb]

private theorem mod_two_q10_certificate :
    ∀ a b : ZMod 2, (a ≠ 0 ∨ b ≠ 0) → divQ10H a b = 1 := by
  decide

private theorem divQ10_ne_zero (x : ℚ) : divQ10 x ≠ 0 := by
  have hpair : (x.num : ZMod 2) ≠ 0 ∨ (x.den : ZMod 2) ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    have hnumInt : (2 : ℤ) ∣ x.num :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 2).mp hnot.1
    have hdenInt : (2 : ℤ) ∣ (x.den : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) 2).mp (by
        simpa using hnot.2)
    have hnum : 2 ∣ x.num.natAbs := Int.natCast_dvd.mp hnumInt
    have hden : 2 ∣ x.den := Int.natCast_dvd.mp hdenInt
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hnum hden) x.reduced
  have hcert := mod_two_q10_certificate (x.num : ZMod 2) (x.den : ZMod 2) hpair
  let A : ℤ := divQ10H x.num (x.den : ℤ)
  have hAmod : (A : ZMod 2) = 1 := by
    simpa [A, divQ10H] using hcert
  have hA0 : A ≠ 0 := by
    intro hzero
    rw [hzero] at hAmod
    norm_num at hAmod
  intro hQzero
  have hdenQ : (x.den : ℚ) ≠ 0 := by positivity
  have hdehom := divQ10H_dehom (x.num : ℚ) (x.den : ℚ) hdenQ
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    simpa using (Rat.num_div_den x).symm
  rw [← hxrepr, hQzero, mul_zero] at hdehom
  have hcast :
      (A : ℚ) = divQ10H (x.num : ℚ) (x.den : ℚ) := by
    norm_num [A, divQ10H]
  rw [← hcast] at hdehom
  exact hA0 (Int.cast_eq_zero.mp hdehom)

private theorem divR_factor (x : ℚ) :
    divR x = x * (x - 1) * divQ10 x := by
  unfold divR divS divP divQ divQ10
  ring

theorem x_eq_zero_or_one_of_five_nsmul_eq_zero
    {x y : ℚ} {h : MinimalCurveBase.Nonsingular x y}
    (hfive : (5 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : MinimalPoint) = 0) :
    x = 0 ∨ x = 1 := by
  have hsame := minimal_five_xrep_same h
  rw [hfive] at hsame
  have hsecond :=
    KeystoneLadder.SameP1Vec.second_eq_zero_of_same_infty (by
      simpa [WeierstrassCurve.Affine.Point.xRep_zero] using hsame)
  have hRsq : divR x ^ 2 = 0 := by
    simpa [KeystoneLadder.xPair, minimalCurve_PsiSq_five_eval] using hsecond
  have hR : divR x = 0 := sq_eq_zero_iff.mp hRsq
  rw [divR_factor] at hR
  rcases mul_eq_zero.mp hR with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · exact (divQ10_ne_zero x h).elim

private theorem mordellToMinimalPointAddEquiv_some
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208) :
    ∃ hmin : MinimalCurveBase.Nonsingular
        ((xi + 12) / 36) ((eta - 108) / 216),
      mordellToMinimalPointAddEquiv (mordellPoint xi eta hcurve) =
        WeierstrassCurve.Affine.Point.some
          ((xi + 12) / 36) ((eta - 108) / 216) hmin := by
  let X : ℚ := variableChangePointX mordellToMinimalChange xi
  let Y : ℚ := variableChangePointY mordellToMinimalChange xi eta
  let hsource : WeierstrassCurve.Affine.Nonsingular mordellCurve xi eta :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((mordellCurve_equation_iff xi eta).2 hcurve)
  let hchanged : WeierstrassCurve.Affine.Nonsingular
      (mordellToMinimalChange • mordellCurve) X Y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (variableChangePoint_equation mordellCurve mordellToMinimalChange
        hsource.left)
  obtain ⟨hminimal, hfirst⟩ :=
    pointCurveEqAddEquiv_some mordellToMinimalChange_smul hchanged
  obtain ⟨hbase, hsecond⟩ :=
    affinePointCurveEqAddEquiv_some minimalCurveBase_eq.symm hminimal
  have hX : X = (xi + 12) / 36 := by
    norm_num [X, variableChangePointX, mordellToMinimalChange]
    ring
  have hY : Y = (eta - 108) / 216 := by
    norm_num [Y, variableChangePointY, mordellToMinimalChange]
    ring
  let hmin : MinimalCurveBase.Nonsingular
      ((xi + 12) / 36) ((eta - 108) / 216) := hX ▸ hY ▸ hbase
  refine ⟨hmin, ?_⟩
  change affinePointCurveEqAddEquiv minimalCurveBase_eq.symm
      (pointCurveEqAddEquiv mordellToMinimalChange_smul
        (Scratch.TateZ2xZ10Reduction.variableChangePointMap
          mordellCurve mordellToMinimalChange (mordellPoint xi eta hcurve))) = _
  have hmap :
      Scratch.TateZ2xZ10Reduction.variableChangePointMap
          mordellCurve mordellToMinimalChange (mordellPoint xi eta hcurve) =
        WeierstrassCurve.Affine.Point.some X Y hchanged := by
    rfl
  rw [hmap, hfirst, hsecond]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hX, hY⟩

private theorem every_mordell_point_has_half
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : WeierstrassCurve.Affine.Point mordellCurve) :
    ∃ Q : WeierstrassCurve.Affine.Point mordellCurve,
      (2 : ℕ) • Q = P := by
  cases P with
  | zero =>
      refine ⟨0, ?_⟩
      simpa only [← WeierstrassCurve.Affine.Point.zero_def] using
        (nsmul_zero 2 : (2 : ℕ) •
          (0 : WeierstrassCurve.Affine.Point mordellCurve) = 0)
  | some xi eta h =>
      have hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208 :=
        (mordellCurve_equation_iff xi eta).1 h.left
      obtain ⟨Q, hQ⟩ :=
        exists_mordell_half_of_factor_square hcurve (hall hcurve)
      refine ⟨Q, ?_⟩
      simpa [mordellPoint] using hQ

private theorem every_minimal_point_has_half
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : MinimalPoint) :
    ∃ Q : MinimalPoint, (2 : ℕ) • Q = P := by
  let F := mordellToMinimalPointAddEquiv
  obtain ⟨R, hR⟩ := every_mordell_point_has_half hall (F.symm P)
  refine ⟨F R, ?_⟩
  calc
    (2 : ℕ) • F R = F ((2 : ℕ) • R) := (map_nsmul F 2 R).symm
    _ = F (F.symm P) := by rw [hR]
    _ = P := F.apply_symm_apply P

private theorem infinitelyTwoDivisible_of_all_factor_square
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    (P : MinimalPoint) : InfinitelyTwoDivisible P := by
  intro n
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨R, hR⟩ := ih
      obtain ⟨Q, hQ⟩ := every_minimal_point_has_half hall R
      refine ⟨Q, ?_⟩
      calc
        (2 ^ (n + 1) : ℕ) • Q = (2 * 2 ^ n : ℕ) • Q := by
          rw [pow_succ, Nat.mul_comm]
        _ = (2 ^ n : ℕ) • ((2 : ℕ) • Q) := mul_nsmul Q 2 (2 ^ n)
        _ = (2 ^ n : ℕ) • R := by rw [hQ]
        _ = P := hR

/-- If every Billing--Mahler cubic factor is a square, 2-adic separatedness
and the fifth division polynomial force every affine point to be a cusp. -/
theorem mordell_x_boundary_of_all_factor_square
    (hall : ∀ {xi eta : ℚ},
      eta ^ 2 = xi ^ 3 - 432 * xi + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0))
    {xi eta : ℚ}
    (hcurve : eta ^ 2 = xi ^ 3 - 432 * xi + 8208) :
    xi = -12 ∨ xi = 24 := by
  let P : WeierstrassCurve.Affine.Point mordellCurve :=
    mordellPoint xi eta hcurve
  let F := mordellToMinimalPointAddEquiv
  have hdiv : InfinitelyTwoDivisible (F P) :=
    infinitelyTwoDivisible_of_all_factor_square hall (F P)
  have hfive : (5 : ℕ) • F P = 0 :=
    five_nsmul_eq_zero_of_infinitelyTwoDivisible hdiv
  obtain ⟨hmin, hmap⟩ := mordellToMinimalPointAddEquiv_some hcurve
  have hfive' : (5 : ℕ) •
      (WeierstrassCurve.Affine.Point.some
        ((xi + 12) / 36) ((eta - 108) / 216) hmin : MinimalPoint) = 0 := by
    simpa only [P, F, hmap] using hfive
  have hX := x_eq_zero_or_one_of_five_nsmul_eq_zero hfive'
  rcases hX with hX | hX
  · left
    linarith
  · right
    linarith

end

noncomputable def alphaInteger : OK :=
  ⟨BillingMahlerField.alpha, BillingMahlerField.alpha_isIntegral⟩

@[simp] theorem alphaInteger_coe_K : (alphaInteger : K) = BillingMahlerField.alpha := by
  rfl

private theorem ofCoords_mul_basis_zero (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (0 : Fin 3) =
      BillingMahlerField.ofCoords a b c := by
  simp [BillingMahlerField.basis_apply]

private theorem ofCoords_mul_basis_one (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (1 : Fin 3) =
      BillingMahlerField.ofCoords (2 * c) (a - 4 * c) (b + 4 * c) := by
  simp [BillingMahlerField.basis_apply]
  unfold BillingMahlerField.ofCoords
  push_cast
  ring_nf
  rw [BillingMahlerField.alpha_cubed]
  norm_num
  ring_nf

private theorem ofCoords_mul_basis_two (a b c : ℚ) :
    BillingMahlerField.ofCoords a b c * BillingMahlerField.basis (2 : Fin 3) =
      BillingMahlerField.ofCoords (2 * b + 8 * c) (-4 * b - 14 * c)
        (a + 4 * b + 12 * c) := by
  simp [BillingMahlerField.basis_apply]
  unfold BillingMahlerField.ofCoords
  push_cast
  ring_nf
  rw [BillingMahlerField.alpha_fourth, BillingMahlerField.alpha_cubed]
  norm_num
  ring_nf

theorem norm_ofCoords (a b c : ℚ) :
    Algebra.norm ℚ (BillingMahlerField.ofCoords a b c) =
      a ^ 3 + 4 * a ^ 2 * b + 8 * a ^ 2 * c + 4 * a * b ^ 2 +
        10 * a * b * c + 2 * b ^ 3 + 8 * b ^ 2 * c +
        8 * b * c ^ 2 + 4 * c ^ 3 := by
  rw [Algebra.norm_eq_matrix_det BillingMahlerField.basis, Matrix.det_fin_three]
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul]
  rw [ofCoords_mul_basis_zero, ofCoords_mul_basis_one, ofCoords_mul_basis_two]
  simp
  ring

theorem cubicPolyInt_aeval_alphaInteger :
    aeval alphaInteger BillingMahlerField.cubicPolyInt = 0 := by
  rw [BillingMahlerField.cubicPolyInt]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
  apply NumberField.RingOfIntegers.ext
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero,
    alphaInteger_coe_K] using BillingMahlerField.alpha_relation

private theorem cubicPolyInt_monic : BillingMahlerField.cubicPolyInt.Monic := by
  unfold BillingMahlerField.cubicPolyInt
  monicity!

private theorem cubicPolyInt_irreducible :
    Irreducible BillingMahlerField.cubicPolyInt := by
  apply (cubicPolyInt_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mpr
  simpa only [BillingMahlerField.cubicPoly] using
    BillingMahlerField.cubicPoly_irreducible

theorem minpoly_alphaInteger :
    minpoly ℤ alphaInteger = BillingMahlerField.cubicPolyInt := by
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd alphaInteger.isIntegral
    cubicPolyInt_aeval_alphaInteger
  have hqUnit : IsUnit q :=
    (cubicPolyInt_irreducible.isUnit_or_isUnit hq).resolve_left
      (minpoly.not_isUnit ℤ alphaInteger)
  have hassociated : Associated BillingMahlerField.cubicPolyInt (minpoly ℤ alphaInteger) := by
    rw [hq]
    simpa only [mul_one] using
      Associated.mul_left (minpoly ℤ alphaInteger)
        (associated_one_iff_isUnit.mpr hqUnit)
  exact (eq_of_monic_of_associated cubicPolyInt_monic
    (minpoly.monic alphaInteger.isIntegral) hassociated).symm

theorem adjoin_alphaInteger_eq_top : Algebra.adjoin ℤ ({alphaInteger} : Set OK) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  let A := Algebra.adjoin ℤ ({alphaInteger} : Set OK)
  have hα : alphaInteger ∈ A :=
    Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton alphaInteger)
  have hbasis : ∀ i : Fin 3, BillingMahlerField.integralPowerBasis i ∈ A := by
    intro i
    fin_cases i
    · have hEq : BillingMahlerField.basisInteger (0 : Fin 3) = 1 := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (0 : Fin 3) = (1 : K)
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (0 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact A.one_mem
    · have hEq : BillingMahlerField.basisInteger (1 : Fin 3) = alphaInteger := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (1 : Fin 3) = BillingMahlerField.alpha
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (1 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact hα
    · have hEq : BillingMahlerField.basisInteger (2 : Fin 3) = alphaInteger ^ 2 := by
        apply NumberField.RingOfIntegers.ext
        change BillingMahlerField.basis (2 : Fin 3) = BillingMahlerField.alpha ^ 2
        simp [BillingMahlerField.basis_apply]
      change BillingMahlerField.integralPowerBasis (2 : Fin 3) ∈ A
      rw [BillingMahlerField.integralPowerBasis_apply, hEq]
      exact A.pow_mem hα 2
  rw [← BillingMahlerField.integralPowerBasis.sum_repr u]
  exact Submodule.sum_mem A.toSubmodule fun i _ ↦
    A.smul_mem (hbasis i) (BillingMahlerField.integralPowerBasis.repr u i)

theorem exponent_alphaInteger_eq_one :
    RingOfIntegers.exponent alphaInteger = 1 := by
  exact RingOfIntegers.exponent_eq_one_iff.mpr adjoin_alphaInteger_eq_top

private theorem basisInteger_zero :
    BillingMahlerField.basisInteger (0 : Fin 3) = 1 := by
  apply NumberField.RingOfIntegers.ext
  change BillingMahlerField.basis (0 : Fin 3) = (1 : K)
  simp [BillingMahlerField.basis_apply]

private theorem basisInteger_one :
    BillingMahlerField.basisInteger (1 : Fin 3) = alphaInteger := by
  apply NumberField.RingOfIntegers.ext
  change BillingMahlerField.basis (1 : Fin 3) = BillingMahlerField.alpha
  simp [BillingMahlerField.basis_apply]

noncomputable def intPolynomial (a b c : ℤ) : OK :=
  algebraMap ℤ OK a + algebraMap ℤ OK b * alphaInteger +
    algebraMap ℤ OK c * alphaInteger ^ 2

theorem descentInteger_eq_intPolynomial (x z : ℤ) :
    BillingMahlerField.descentInteger x z =
      algebraMap ℤ OK (x - 24 * z ^ 2) +
        algebraMap ℤ OK (18 * z ^ 2) * alphaInteger := by
  apply NumberField.RingOfIntegers.ext
  rw [BillingMahlerField.descentInteger_coe_K]
  simp [BillingMahlerField.descentElement, BillingMahlerField.ofCoords,
    BillingMahlerField.basis_apply]
  norm_num [map_ofNat]

theorem exists_intPolynomial_coords (u : OK) :
    ∃ a b c : ℤ, u = intPolynomial a b c := by
  obtain ⟨a, b, c, hu⟩ := BillingMahlerField.ringOfIntegers_exists_integer_coords u
  refine ⟨a, b, c, ?_⟩
  unfold intPolynomial
  apply NumberField.RingOfIntegers.ext
  change (u : K) =
    algebraMap ℤ K a + algebraMap ℤ K b * BillingMahlerField.alpha +
      algebraMap ℤ K c * BillingMahlerField.alpha ^ 2
  simpa [BillingMahlerField.ofCoords] using hu

theorem absNorm_descentInteger_span
    (x z y : ℤ)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    Ideal.absNorm (Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK)) =
      y.natAbs ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hnorm : Algebra.norm ℤ (BillingMahlerField.descentInteger x z) = y ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, BillingMahlerField.descentInteger_coe_K,
      BillingMahlerField.norm_descentElement, ← hmodel]
  rw [hnorm, Int.natAbs_pow]

private theorem prime_not_dvd_eighteen {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ (p : ℤ) ∣ 18 := by
  intro h
  have hnat : p ∣ 18 := by exact_mod_cast h
  have hle : p ≤ 18 := Nat.le_of_dvd (by norm_num) hnat
  interval_cases p <;> norm_num at *

noncomputable def descentResidue (p : ℕ) [Fact p.Prime] (x z : ℤ) :
    ResidueInt p :=
  -(algebraMap ℤ (ResidueInt p) (x - 24 * z ^ 2)) /
    algebraMap ℤ (ResidueInt p) (18 * z ^ 2)

noncomputable def residueEval (p : ℕ) [Fact p.Prime]
    (x z a b c : ℤ) : ResidueInt p :=
  algebraMap ℤ (ResidueInt p) a +
    algebraMap ℤ (ResidueInt p) b * descentResidue p x z +
    algebraMap ℤ (ResidueInt p) c * descentResidue p x z ^ 2

private theorem mem_intPolynomial_iff_residueEval_eq_zero
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z a b c : ℤ)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halpha : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z)) :
    intPolynomial a b c ∈ P ↔ residueEval p x z a b c = 0 := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  have heval :
      Ideal.Quotient.mk P (intPolynomial a b c) =
        algebraMap (ResidueInt p) (OK ⧸ P) (residueEval p x z a b c) := by
    simp only [intPolynomial, residueEval, map_add, map_mul, map_pow, hmap, halpha]
  rw [← Ideal.Quotient.eq_zero_iff_mem, heval]
  constructor
  · intro h
    apply FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P)
    simpa using h
  · intro h
    rw [h]
    exact map_zero _

private theorem inertiaDeg_eq_one_of_alpha_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z : ℤ) (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halpha : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z)) :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P = 1 := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  rw [Ideal.inertiaDeg'_algebraMap]
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  refine ⟨FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P), ?_⟩
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  intro q
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, b, c, hu⟩ := exists_intPolynomial_coords u
  refine ⟨residueEval p x z a b c, ?_⟩
  rw [hu]
  simp only [intPolynomial, residueEval, map_add, map_mul, map_pow,
    halpha, hmap]

private theorem primes_eq_of_alpha_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (x z : ℤ) (P Q : Ideal OK)
    [P.IsPrime] [NeZero P] [Q.IsPrime] [NeZero Q]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (halphaP : Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z))
    (halphaQ : Ideal.Quotient.mk Q alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ Q) (descentResidue p x z)) :
    P = Q := by
  apply le_antisymm
  · intro u hu
    obtain ⟨a, b, c, habc⟩ := exists_intPolynomial_coords u
    rw [habc] at hu ⊢
    exact (mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c Q halphaQ).mpr
      ((mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c P halphaP).mp hu)
  · intro u hu
    obtain ⟨a, b, c, habc⟩ := exists_intPolynomial_coords u
    rw [habc] at hu ⊢
    exact (mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c P halphaP).mpr
      ((mem_intPolynomial_iff_residueEval_eq_zero hp x z a b c Q halphaQ).mp hu)

private theorem descentResidue_two_eq_zero (x z : ℤ) :
    descentResidue 2 x z = 0 := by
  have hden : algebraMap ℤ (ResidueInt 2) (18 * z ^ 2) = 0 := by
    change Ideal.Quotient.mk (Ideal.span ({(2 : ℤ)} : Set ℤ)) (18 * z ^ 2) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨9 * z ^ 2, by ring⟩
  rw [descentResidue, hden, div_zero]

private theorem alpha_mem_prime_above_two
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))] :
    alphaInteger ∈ P := by
  have h2under : (2 : ℤ) ∈ P.under ℤ := by
    rw [← P.over_def (Ideal.span ({(2 : ℤ)} : Set ℤ))]
    exact Ideal.mem_span_singleton_self 2
  have h2P : algebraMap ℤ OK 2 ∈ P := by
    rw [← Ideal.mem_under]
    exact h2under
  have h4P : algebraMap ℤ OK 4 ∈ P := by
    have := P.mul_mem_left (algebraMap ℤ OK 2) h2P
    norm_num [← map_mul] at this ⊢
    exact this
  have hrel : alphaInteger ^ 3 =
      algebraMap ℤ OK 4 * alphaInteger ^ 2 -
        algebraMap ℤ OK 4 * alphaInteger + algebraMap ℤ OK 2 := by
    apply NumberField.RingOfIntegers.ext
    change BillingMahlerField.alpha ^ 3 =
      algebraMap ℤ K 4 * BillingMahlerField.alpha ^ 2 -
        algebraMap ℤ K 4 * BillingMahlerField.alpha + algebraMap ℤ K 2
    norm_num [map_ofNat]
    exact BillingMahlerField.alpha_cubed
  have halpha3 : alphaInteger ^ 3 ∈ P := by
    rw [hrel]
    exact P.add_mem
      (P.sub_mem (P.mul_mem_right _ h4P) (P.mul_mem_right _ h4P)) h2P
  exact (inferInstance : P.IsPrime).mem_of_pow_mem 3 halpha3

private theorem alpha_mod_prime_above_two_eq_descentResidue
    (x z : ℤ) (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))] :
    Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt 2) (OK ⧸ P) (descentResidue 2 x z) := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  rw [descentResidue_two_eq_zero, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (alpha_mem_prime_above_two P)

private theorem cubicPoly_mod_three_irreducible :
    Irreducible
      (BillingMahlerField.cubicPolyInt.map (Int.castRingHom (ZMod 3))) := by
  let f : (ZMod 3)[X] := X ^ 3 + 2 * X ^ 2 + X + 1
  have hf : BillingMahlerField.cubicPolyInt.map (Int.castRingHom (ZMod 3)) = f := by
    simp [BillingMahlerField.cubicPolyInt, f]
    have hthree : (3 : (ZMod 3)[X]) = 0 := by
      change C (3 : ZMod 3) = 0
      rw [show (3 : ZMod 3) = 0 by decide, map_zero]
    linear_combination (-2 * X ^ 2 + X - 1) * hthree
  rw [hf]
  have hfmonic : f.Monic := by
    dsimp [f]
    monicity!
  have hfdeg : f.natDegree = 3 := by
    dsimp [f]
    compute_degree <;> norm_num
  apply (hfmonic.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega) (by omega)).mpr
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro r
  rw [mem_roots hfmonic.ne_zero]
  fin_cases r
  · have hval : eval (0 : ZMod 3) f = 1 := by simp [f]
    change eval (0 : ZMod 3) f ≠ 0
    rw [hval]
    exact one_ne_zero
  · have hval : eval (1 : ZMod 3) f = 2 := by
      simp [f]
      decide
    change eval (1 : ZMod 3) f ≠ 0
    rw [hval]
    decide
  · have hval : eval (2 : ZMod 3) f = 1 := by
      simp [f]
      decide
    change eval (2 : ZMod 3) f ≠ 0
    rw [hval]
    exact one_ne_zero

private theorem span_three_isMaximal :
    (Ideal.span ({(3 : OK)} : Set OK)).IsMaximal := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let m3 : (ZMod 3)[X] :=
    (minpoly ℤ alphaInteger).map (Int.castRingHom (ZMod 3))
  have hm3 : Irreducible m3 := by
    simpa [m3, minpoly_alphaInteger] using cubicPoly_mod_three_irreducible
  letI : Fact (Irreducible m3) := ⟨hm3⟩
  have hexponent : ¬ 3 ∣ RingOfIntegers.exponent alphaInteger := by
    rw [exponent_alphaInteger_eq_one]
    norm_num
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan
    (K := K) (p := 3) (θ := alphaInteger) hexponent
  apply Ideal.Quotient.maximal_of_isField
  exact e.symm.toMulEquiv.isField (Field.toIsField _)

private theorem prime_above_three_eq_span
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))] :
    P = Ideal.span ({(3 : OK)} : Set OK) := by
  apply Eq.symm
  apply Ideal.IsMaximal.eq_of_le span_three_isMaximal
    (inferInstance : P.IsPrime).ne_top
  rw [Ideal.span_singleton_le_iff_mem]
  have h3under : (3 : ℤ) ∈ P.under ℤ := by
    rw [← P.over_def (Ideal.span ({(3 : ℤ)} : Set ℤ))]
    exact Ideal.mem_span_singleton_self 3
  change algebraMap ℤ OK 3 ∈ P
  rw [← Ideal.mem_under]
  exact h3under

private theorem inertiaDeg_prime_above_three
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ))] :
    (Ideal.span ({(3 : ℤ)} : Set ℤ)).inertiaDeg' P = 3 := by
  have hnorm : Ideal.absNorm P = 3 ^ 3 := by
    rw [prime_above_three_eq_span P]
    calc
      Ideal.absNorm (Ideal.span ({(3 : OK)} : Set OK)) =
          3 ^ Module.finrank ℤ OK := by
        simpa using (Ideal.absNorm_span_natCast (S := OK) 3)
      _ = 3 ^ 3 := by
        rw [NumberField.RingOfIntegers.rank, BillingMahlerField.finrank_K]
  have hpow := Ideal.absNorm_eq_pow_inertiaDeg' P (by norm_num : Nat.Prime 3)
  rw [hnorm] at hpow
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow.symm

private theorem normalized_factor_count_even_of_unique_odd_inertia
    (J : Ideal OK) (hJ : J ≠ ⊥) (n : ℕ)
    (hJnorm : Ideal.absNorm J = n ^ 2)
    (P : Ideal OK) (hPmem : P ∈ normalizedFactors J)
    (hodd : Odd
      ((Ideal.span ({(Ideal.absNorm (P.under ℤ) : ℤ)} : Set ℤ)).inertiaDeg' P))
    (hunique : ∀ Q : Ideal OK, Q ∈ normalizedFactors J →
      Ideal.absNorm (Q.under ℤ) = Ideal.absNorm (P.under ℤ) → Q = P) :
    Even ((normalizedFactors J).count P) := by
  let p := Ideal.absNorm (P.under ℤ)
  let k := (normalizedFactors J).count P
  have hPprime : Prime P := prime_of_normalized_factor P hPmem
  letI : P.IsPrime := Ideal.isPrime_of_prime hPprime
  letI : NeZero P := ⟨hPprime.ne_zero⟩
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  have hp : p.Prime := Nat.absNorm_under_prime P
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hPR, hdecomp⟩ := Ideal.eq_prime_pow_mul_coprime hJ P
  have hR : R ≠ ⊥ := by
    intro hR
    apply hJ
    calc
      J = P ^ (Multiset.count P (normalizedFactors J)) * R := hdecomp
      _ = ⊥ := by simp [hR]
  have hRnorm : Ideal.absNorm R ≠ 0 := by
    intro hnorm
    exact hR (Ideal.absNorm_eq_zero_iff.mp hnorm)
  have hpR : ¬ p ∣ Ideal.absNorm R := by
    intro hpR
    obtain ⟨Q, hQmax, hQunder, hQdvd⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp R hpR
    have hJleR : J ≤ R := by
      rw [hdecomp]
      exact Ideal.mul_le_right
    have hRleQ : R ≤ Q := Ideal.dvd_iff_le.mp hQdvd
    have hQmem : Q ∈ normalizedFactors J :=
      (Ideal.mem_normalizedFactors_iff hJ).mpr
        ⟨hQmax.isPrime, hJleR.trans hRleQ⟩
    have hQnorm : Ideal.absNorm (Q.under ℤ) = p := by
      rw [hQunder]
      simp
    have hQP : Q = P := hunique Q hQmem hQnorm
    have hRleP : R ≤ P := by simpa only [hQP] using hRleQ
    rw [sup_eq_left.mpr hRleP] at hPR
    exact (inferInstance : P.IsPrime).ne_top hPR
  have hPnorm : Ideal.absNorm P =
      p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P) :=
    Ideal.absNorm_eq_pow_inertiaDeg' P hp
  have hnormDecomp : Ideal.absNorm J =
      (p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P)) ^ k *
        Ideal.absNorm R := by
    rw [hdecomp, map_mul, map_pow, hPnorm]
  have hpne : p ≠ 0 := hp.ne_zero
  have hPpowne :
      (p ^ ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P)) ^ k ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hpne)
  have hfactor : (Ideal.absNorm J).factorization p =
      k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P) := by
    rw [hnormDecomp, Nat.factorization_mul hPpowne hRnorm,
      Nat.factorization_pow, Nat.Prime.factorization_pow hp]
    simp [Nat.factorization_eq_zero_of_not_dvd hpR, mul_comm]
  have hfactorEven : Even ((Ideal.absNorm J).factorization p) := by
    refine ⟨n.factorization p, ?_⟩
    rw [hJnorm, Nat.factorization_pow]
    simp [two_nsmul]
  have hkMulEven : Even
      (k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P)) := by
    rw [← hfactor]
    exact hfactorEven
  by_contra hk
  have hkOdd : Odd k := Nat.not_even_iff_odd.mp hk
  have hprodOdd : Odd
      (k * ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P)) :=
    hkOdd.mul hodd
  exact (Nat.not_even_iff_odd.mpr hprodOdd) hkMulEven

private theorem alpha_mod_prime_eq_descentResidue
    {p : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (x z : ℤ) (hpz : ¬ (p : ℤ) ∣ z)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hdelta : BillingMahlerField.descentInteger x z ∈ P) :
    Ideal.Quotient.mk P alphaInteger =
      algebraMap (ResidueInt p) (OK ⧸ P) (descentResidue p x z) := by
  letI : P.IsMaximal :=
    (inferInstance : P.IsPrime).isMaximal (NeZero.ne P)
  let A : ℤ := x - 24 * z ^ 2
  let B : ℤ := 18 * z ^ 2
  have hpB : ¬ (p : ℤ) ∣ B := by
    intro hB
    have hcases : (p : ℤ) ∣ 18 ∨ (p : ℤ) ∣ z ^ 2 :=
      (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (by simpa [B] using hB)
    rcases hcases with h18 | hz2
    · exact prime_not_dvd_eighteen hp hp2 hp3 h18
    · exact hpz ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hz2)
  have hB0 : algebraMap ℤ (ResidueInt p) B ≠ 0 := by
    change Ideal.Quotient.mk (Ideal.span ({(p : ℤ)} : Set ℤ)) B ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hpB
  have hzero :
      Ideal.Quotient.mk P (BillingMahlerField.descentInteger x z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hdelta
  have hmap (n : ℤ) :
      Ideal.Quotient.mk P (algebraMap ℤ OK n) =
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) n) := by
    change algebraMap ℤ (OK ⧸ P) n = _
    exact IsScalarTower.algebraMap_apply ℤ (ResidueInt p) (OK ⧸ P) n
  have hzero' :
      algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) A) +
        algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) B) *
          Ideal.Quotient.mk P alphaInteger = 0 := by
    rw [descentInteger_eq_intPolynomial] at hzero
    change Ideal.Quotient.mk P (algebraMap ℤ OK A) +
        Ideal.Quotient.mk P (algebraMap ℤ OK B) *
          Ideal.Quotient.mk P alphaInteger = 0 at hzero
    rw [hmap A, hmap B] at hzero
    exact hzero
  have hBE :
      algebraMap (ResidueInt p) (OK ⧸ P)
          (algebraMap ℤ (ResidueInt p) B) ≠ 0 :=
    by
      intro h
      apply hB0
      apply FaithfulSMul.algebraMap_injective (ResidueInt p) (OK ⧸ P)
      simpa using h
  change Ideal.Quotient.mk P alphaInteger =
    algebraMap (ResidueInt p) (OK ⧸ P)
      (-(algebraMap ℤ (ResidueInt p) A) /
        algebraMap ℤ (ResidueInt p) B)
  rw [map_div₀ (algebraMap (ResidueInt p) (OK ⧸ P)), map_neg,
    eq_div_iff hBE]
  linear_combination hzero'

private theorem prime_below_not_dvd_z
    (x z : ℤ) (hcop : Int.gcd x z = 1)
    (P : Ideal OK) [P.IsPrime] [NeZero P]
    (hdelta : BillingMahlerField.descentInteger x z ∈ P) :
    ¬ (Ideal.absNorm (P.under ℤ) : ℤ) ∣ z := by
  intro hpz
  let p := Ideal.absNorm (P.under ℤ)
  have hzP : algebraMap ℤ OK z ∈ P :=
    (Int.cast_mem_ideal_iff (I := P)).mpr hpz
  have hz2P : algebraMap ℤ OK (z ^ 2) ∈ P := by
    simpa only [map_pow] using P.pow_mem_of_mem hzP 2 (by norm_num)
  have h24P : algebraMap ℤ OK (24 * z ^ 2) ∈ P := by
    rw [map_mul]
    exact P.mul_mem_left _ hz2P
  have h18P : algebraMap ℤ OK (18 * z ^ 2) * alphaInteger ∈ P := by
    rw [map_mul]
    exact P.mul_mem_right _ (P.mul_mem_left _ hz2P)
  have hxP : algebraMap ℤ OK x ∈ P := by
    rw [descentInteger_eq_intPolynomial] at hdelta
    have heq : algebraMap ℤ OK x =
        (algebraMap ℤ OK (x - 24 * z ^ 2) +
          algebraMap ℤ OK (18 * z ^ 2) * alphaInteger) +
          algebraMap ℤ OK (24 * z ^ 2) -
          algebraMap ℤ OK (18 * z ^ 2) * alphaInteger := by
      push_cast
      ring
    rw [heq]
    exact P.sub_mem (P.add_mem hdelta h24P) h18P
  have hpx : (p : ℤ) ∣ x := (Int.cast_mem_ideal_iff (I := P)).mp hxP
  have hp : p.Prime := Nat.absNorm_under_prime P
  have hcop' : IsCoprime x z := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact (Nat.prime_iff_prime_int.mp hp).not_unit
    (hcop'.isUnit_of_dvd' hpx hpz)

private theorem ideal_square_of_even_factor_counts
    (J : Ideal OK) (hJ : J ≠ ⊥)
    (heven : ∀ P : Ideal OK, Even ((normalizedFactors J).count P)) :
    ∃ I : Ideal OK, J = I ^ 2 := by
  classical
  obtain ⟨M, hM⟩ := Multiset.exists_smul_of_dvd_count (normalizedFactors J)
    (k := 2) (fun P hP ↦ (heven P).two_dvd)
  refine ⟨M.prod, ?_⟩
  calc
    J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self hJ).symm
    _ = (2 • M).prod := by rw [hM]
    _ = M.prod ^ 2 := Multiset.prod_nsmul M 2

/-- The principal ideal generated by the Billing--Mahler cubic factor is an
ideal square for every nonzero primitive solution of the Mordell model. -/
theorem descentInteger_span_eq_sq
    (x z y : ℤ) (hcop : Int.gcd x z = 1) (hy : y ≠ 0)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    ∃ I : Ideal OK,
      Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK) = I ^ 2 := by
  classical
  let J : Ideal OK :=
    Ideal.span ({BillingMahlerField.descentInteger x z} : Set OK)
  have hJnorm : Ideal.absNorm J = y.natAbs ^ 2 := by
    exact absNorm_descentInteger_span x z y hmodel
  have hynat : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  have hJ : J ≠ ⊥ := by
    intro hbot
    have hzero : y.natAbs ^ 2 = 0 := by
      rw [← hJnorm, hbot]
      simp
    exact (pow_ne_zero 2 hynat) hzero
  apply ideal_square_of_even_factor_counts J hJ
  intro P
  by_cases hPmem : P ∈ normalizedFactors J
  · let p := Ideal.absNorm (P.under ℤ)
    have hPprime : Prime P := prime_of_normalized_factor P hPmem
    letI : P.IsPrime := Ideal.isPrime_of_prime hPprime
    letI : NeZero P := ⟨hPprime.ne_zero⟩
    have hp : p.Prime := Nat.absNorm_under_prime P
    letI : Fact p.Prime := ⟨hp⟩
    letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      dsimp [p]
      infer_instance
    have hdelta : BillingMahlerField.descentInteger x z ∈ P := by
      have hJleP := (Ideal.mem_normalizedFactors_iff hJ).mp hPmem |>.2
      exact hJleP (Ideal.subset_span (Set.mem_singleton _))
    have hpz : ¬ (p : ℤ) ∣ z := by
      simpa only [p] using prime_below_not_dvd_z x z hcop P hdelta
    have hodd : Odd
        ((Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P) := by
      rcases eq_or_ne p 2 with hp2 | hp2
      · letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        have halpha := alpha_mod_prime_above_two_eq_descentResidue x z P
        have hinertia :
            (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P = 1 := by
          simpa [hp2] using
            inertiaDeg_eq_one_of_alpha_eq_descentResidue (by norm_num) x z P halpha
        rw [hinertia]
        exact odd_one
      · rcases eq_or_ne p 3 with hp3 | hp3
        · letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          have hinertia :
              (Ideal.span ({(p : ℤ)} : Set ℤ)).inertiaDeg' P = 3 := by
            simpa [hp3] using inertiaDeg_prime_above_three P
          rw [hinertia]
          exact ⟨1, by norm_num⟩
        · have halpha := alpha_mod_prime_eq_descentResidue
            hp hp2 hp3 x z hpz P hdelta
          rw [inertiaDeg_eq_one_of_alpha_eq_descentResidue hp x z P halpha]
          exact odd_one
    have hunique : ∀ Q : Ideal OK, Q ∈ normalizedFactors J →
        Ideal.absNorm (Q.under ℤ) = p → Q = P := by
      intro Q hQmem hQnorm
      have hQprime : Prime Q := prime_of_normalized_factor Q hQmem
      letI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
      letI : NeZero Q := ⟨hQprime.ne_zero⟩
      letI : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
        rw [← hQnorm]
        infer_instance
      rcases eq_or_ne p 2 with hp2 | hp2
      · letI : Q.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
          simpa [hp2] using
            (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
        exact primes_eq_of_alpha_eq_descentResidue (by norm_num) x z Q P
          (alpha_mod_prime_above_two_eq_descentResidue x z Q)
          (alpha_mod_prime_above_two_eq_descentResidue x z P)
      · rcases eq_or_ne p 3 with hp3 | hp3
        · letI : Q.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
            simpa [hp3] using
              (inferInstance : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
          calc
            Q = Ideal.span ({(3 : OK)} : Set OK) := prime_above_three_eq_span Q
            _ = P := (prime_above_three_eq_span P).symm
        · have hQdelta : BillingMahlerField.descentInteger x z ∈ Q := by
            have hJleQ := (Ideal.mem_normalizedFactors_iff hJ).mp hQmem |>.2
            exact hJleQ (Ideal.subset_span (Set.mem_singleton _))
          exact primes_eq_of_alpha_eq_descentResidue hp x z Q P
            (alpha_mod_prime_eq_descentResidue hp hp2 hp3 x z hpz Q hQdelta)
            (alpha_mod_prime_eq_descentResidue hp hp2 hp3 x z hpz P hdelta)
    exact normalized_factor_count_even_of_unique_odd_inertia
      J hJ y.natAbs hJnorm P hPmem (by simpa only [p] using hodd)
        (by simpa only [p] using hunique)
  · rw [Multiset.count_eq_zero.mpr hPmem]
    exact ⟨0, by simp⟩

end MazurProof.RationalPointsN11IdealSquare

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsN11.lean, lines 16-22. -/
section

namespace MazurProof.RationalPointsN11

def E11AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16

def E11DegenerateParameter (X : ℚ) : Prop :=
  X = 0 ∨ X = -4

end MazurProof.RationalPointsN11

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/CyclicExclusion11.lean, lines 247-529. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion11

/--
The remaining global input in the Billing--Mahler proof, after denominator
normalization and all explicit cubic-field algebra.

For a primitive integral model, either the original rational point is an
integral Lutz--Nagell exceptional point, or the global descent supplies an
ideal square and a nonsquare cubic factor.  The class-number-one theorem, the
integral basis, the four unit squareclasses, selection of the `epsilon` class,
and the coefficient expansion are proved in `BillingMahlerField`.
-/
private theorem descentElement_isSquare_of_primitive_model
    (x z y : ℤ) (hcop : Int.gcd x z = 1) (hy : y ≠ 0)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    IsSquare (BillingMahlerField.descentElement x z) := by
  obtain ⟨I, hideal⟩ :=
    RationalPointsN11IdealSquare.descentInteger_span_eq_sq
      x z y hcop hy hmodel
  obtain ⟨w, hw | hw | hw | hw⟩ :=
    BillingMahlerField.descentInteger_four_squareclasses_of_ideal_square
      x z I hideal
  · refine ⟨(w : BillingMahlerField.K), ?_⟩
    simpa [pow_two] using congrArg
      (fun q : NumberField.RingOfIntegers BillingMahlerField.K ↦
        (q : BillingMahlerField.K)) hw
  · have hwK : BillingMahlerField.descentElement x z =
        -((w : BillingMahlerField.K) ^ 2) := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers BillingMahlerField.K ↦
          (q : BillingMahlerField.K)) hw
    have hnormPos : 0 <
        Algebra.norm ℚ (BillingMahlerField.descentElement x z) := by
      rw [BillingMahlerField.norm_descentElement, ← hmodel]
      exact_mod_cast sq_pos_of_ne_zero hy
    have hnormNonpos :
        Algebra.norm ℚ (-((w : BillingMahlerField.K) ^ 2)) ≤ 0 := by
      rw [show -((w : BillingMahlerField.K) ^ 2) =
          algebraMap ℚ BillingMahlerField.K (-1) * (w : BillingMahlerField.K) ^ 2 by
            simp,
        map_mul, Algebra.norm_algebraMap, map_pow, BillingMahlerField.finrank_K]
      norm_num
      positivity
    rw [← hwK] at hnormNonpos
    linarith
  · have hwK : BillingMahlerField.descentElement x z =
        BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2 := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers BillingMahlerField.K ↦
          (q : BillingMahlerField.K)) hw
    obtain ⟨a, b, c, habc⟩ :=
      BillingMahlerField.ringOfIntegers_exists_thetaBasis_coords
        (BillingMahlerField.epsilonInteger * w)
    have hsquare :
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
          BillingMahlerField.thetaBasisElement a b c ^ 2 := by
      calc
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
            BillingMahlerField.epsilon *
              (BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2) := by
                rw [hwK]
        _ = (((BillingMahlerField.epsilonInteger * w :
              NumberField.RingOfIntegers BillingMahlerField.K) :
                BillingMahlerField.K)) ^ 2 := by
              simp
              ring
        _ = BillingMahlerField.thetaBasisElement a b c ^ 2 := by rw [habc]
    have hcoeff :=
      BillingMahlerField.coefficient_system_of_epsilon_mul_descentElement_eq_sq
        x z a b c hsquare
    exact (RationalPointsN11Descent.no_billing_mahler_coefficient_system
      x z a b c hcop hcoeff.1 hcoeff.2.1 hcoeff.2.2).elim
  · have hwK : BillingMahlerField.descentElement x z =
        -BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2 := by
      simpa using congrArg
        (fun q : NumberField.RingOfIntegers BillingMahlerField.K ↦
          (q : BillingMahlerField.K)) hw
    have hnormPos : 0 <
        Algebra.norm ℚ (BillingMahlerField.descentElement x z) := by
      rw [BillingMahlerField.norm_descentElement, ← hmodel]
      exact_mod_cast sq_pos_of_ne_zero hy
    have hnormNonpos : Algebra.norm ℚ
        (-BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2) ≤ 0 := by
      rw [show -BillingMahlerField.epsilon =
          algebraMap ℚ BillingMahlerField.K (-1) *
            BillingMahlerField.epsilon by simp,
        mul_assoc, map_mul, map_mul, Algebra.norm_algebraMap,
        BillingMahlerField.norm_epsilon, map_pow, BillingMahlerField.finrank_K]
      norm_num
      positivity
    rw [← hwK] at hnormNonpos
    linarith

private theorem primitive_model_y_ne_zero
    (x z y : ℤ) (hz : 0 < z)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    y ≠ 0 := by
  intro hy
  have hnorm :
      Algebra.norm ℚ (BillingMahlerField.descentElement x z) = 0 := by
    rw [BillingMahlerField.norm_descentElement, ← hmodel, hy]
    norm_num
  have hzero : BillingMahlerField.descentElement x z = 0 :=
    (Algebra.norm_eq_zero_iff (R := ℚ)).1 hnorm
  have hone := congrArg
    (fun q : BillingMahlerField.K ↦
      BillingMahlerField.basis.repr q (1 : Fin 3)) hzero
  simp only [BillingMahlerField.descentElement,
    BillingMahlerField.basis_repr_ofCoords_one, map_zero] at hone
  push_cast at hone
  have hzsq : (z : ℚ) ^ 2 = 0 :=
    (mul_eq_zero.mp hone).resolve_left (by norm_num)
  have hzq : (z : ℚ) = 0 := sq_eq_zero_iff.mp hzsq
  exact (Int.cast_ne_zero.mpr (ne_of_gt hz)) hzq

private theorem factor_square_of_descentElement_square
    {xi : ℚ} (x z : ℤ) (hz : 0 < z)
    (hxi : xi = (x : ℚ) / (z : ℚ) ^ 2)
    (hsquare : IsSquare (BillingMahlerField.descentElement x z)) :
    IsSquare (BillingMahlerField.ofCoords (xi - 24) 18 0) := by
  have hzq : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hz)
  have hzK : algebraMap ℚ BillingMahlerField.K (z : ℚ) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ BillingMahlerField.K)).2 hzq
  have hscale :
      BillingMahlerField.descentElement x z =
        (algebraMap ℚ BillingMahlerField.K (z : ℚ)) ^ 2 *
          BillingMahlerField.ofCoords (xi - 24) 18 0 := by
    unfold BillingMahlerField.descentElement BillingMahlerField.ofCoords
    rw [hxi]
    push_cast
    field_simp [hzq, hzK]
    ring
  rcases hsquare with ⟨w, hw⟩
  refine ⟨w / algebraMap ℚ BillingMahlerField.K (z : ℚ), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hzK)
  calc
    (algebraMap ℚ BillingMahlerField.K (z : ℚ)) ^ 2 *
          BillingMahlerField.ofCoords (xi - 24) 18 0 =
        BillingMahlerField.descentElement x z := hscale.symm
    _ = w * w := hw
    _ = (algebraMap ℚ BillingMahlerField.K (z : ℚ)) ^ 2 *
        ((w / algebraMap ℚ BillingMahlerField.K (z : ℚ)) *
          (w / algebraMap ℚ BillingMahlerField.K (z : ℚ))) := by
      field_simp [hzK]

theorem billing_mahler_global_descent
    {ξ η : ℚ} (hcurve : RationalPointsN11Descent.MordellEquation ξ η)
    (x z y : ℤ) (hz : 0 < z) (hcop : Int.gcd x z = 1)
    (hξ : ξ = (x : ℚ) / (z : ℚ) ^ 2)
    (hmodel : y ^ 2 = x ^ 3 - 432 * x * z ^ 4 + 8208 * z ^ 6) :
    (∃ x y : ℤ,
      ξ = (x : ℚ) ∧ η = (y : ℚ) ∧
        (y ^ 2 = 0 ∨ y ^ 2 ∣
          (RationalPointsN11Descent.mordellDiscriminantAbs : ℤ))) ∨
      ∃ I : Ideal (NumberField.RingOfIntegers BillingMahlerField.K),
        y ≠ 0 ∧
          Ideal.span ({BillingMahlerField.descentInteger x z} :
              Set (NumberField.RingOfIntegers BillingMahlerField.K)) = I ^ 2 ∧
          ¬ IsSquare (BillingMahlerField.descentElement x z) := by
  have hall : ∀ {xi' eta' : ℚ},
      eta' ^ 2 = xi' ^ 3 - 432 * xi' + 8208 →
        IsSquare (BillingMahlerField.ofCoords (xi' - 24) 18 0) := by
    intro xi' eta' hcurve'
    by_cases hsame : xi' = ξ
    · subst xi'
      have hy : y ≠ 0 := primitive_model_y_ne_zero x z y hz hmodel
      have hsquare : IsSquare (BillingMahlerField.descentElement x z) :=
        descentElement_isSquare_of_primitive_model x z y hcop hy hmodel
      exact factor_square_of_descentElement_square x z hz hξ hsquare
    · obtain ⟨x', z', y', hz', hcop', hxi', hmodel'⟩ :=
        RationalPointsN11Descent.mordell_integral_model_of_rational_point
          xi' eta' hcurve'
      have hy' : y' ≠ 0 := primitive_model_y_ne_zero x' z' y' hz' hmodel'
      have hsquare : IsSquare (BillingMahlerField.descentElement x' z') :=
        descentElement_isSquare_of_primitive_model
          x' z' y' hcop' hy' hmodel'
      exact factor_square_of_descentElement_square x' z' hz' hxi' hsquare
  have hboundary : ξ = -12 ∨ ξ = 24 :=
    RationalPointsN11IdealSquare.mordell_x_boundary_of_all_factor_square
      hall hcurve
  left
  rcases hboundary with hxi | hxi
  · have hetaSq : η ^ 2 = (108 : ℚ) ^ 2 := by
      calc
        η ^ 2 = ξ ^ 3 - 432 * ξ + 8208 := hcurve
        _ = (108 : ℚ) ^ 2 := by rw [hxi]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hetaSq with heta | heta
    · refine ⟨-12, 108, ?_, ?_, Or.inr ?_⟩
      · simpa using hxi
      · simpa using heta
      · norm_num [RationalPointsN11Descent.mordellDiscriminantAbs]
    · refine ⟨-12, -108, ?_, ?_, Or.inr ?_⟩
      · simpa using hxi
      · simpa using heta
      · norm_num [RationalPointsN11Descent.mordellDiscriminantAbs]
  · have hetaSq : η ^ 2 = (108 : ℚ) ^ 2 := by
      calc
        η ^ 2 = ξ ^ 3 - 432 * ξ + 8208 := hcurve
        _ = (108 : ℚ) ^ 2 := by rw [hxi]; norm_num
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hetaSq with heta | heta
    · refine ⟨24, 108, ?_, ?_, Or.inr ?_⟩
      · simpa using hxi
      · simpa using heta
      · norm_num [RationalPointsN11Descent.mordellDiscriminantAbs]
    · refine ⟨24, -108, ?_, ?_, Or.inr ?_⟩
      · simpa using hxi
      · simpa using heta
      · norm_num [RationalPointsN11Descent.mordellDiscriminantAbs]

/-- The global seam above implies the exact arithmetic dichotomy consumed by
the already-checked exceptional enumeration and parity contradiction. -/
theorem billing_mahler_rational_point_dichotomy
    {ξ η : ℚ} (hcurve : RationalPointsN11Descent.MordellEquation ξ η) :
    (∃ x y : ℤ,
      ξ = (x : ℚ) ∧ η = (y : ℚ) ∧
        (y ^ 2 = 0 ∨ y ^ 2 ∣
          (RationalPointsN11Descent.mordellDiscriminantAbs : ℤ))) ∨
      ∃ x z a b c : ℤ,
        Int.gcd x z = 1 ∧
          -x + 24 * z ^ 2 = a ^ 2 + 4 * b * c ∧
          18 * z ^ 2 = c ^ 2 + 2 * a * b + 4 * b * c ∧
          x = 2 * (b ^ 2 + c ^ 2 + a * c + 3 * z ^ 2) := by
  obtain ⟨x, z, y, hz, hcop, hξ, hmodel⟩ :=
    RationalPointsN11Descent.mordell_integral_model_of_rational_point ξ η hcurve
  rcases billing_mahler_global_descent hcurve x z y hz hcop hξ hmodel with
    hexceptional | ⟨I, hy, hideal, hnonsquare⟩
  · exact Or.inl hexceptional
  · have hnorm : 0 < Algebra.norm ℚ (BillingMahlerField.descentElement x z) := by
      rw [BillingMahlerField.norm_descentElement, ← hmodel]
      exact_mod_cast sq_pos_of_ne_zero hy
    obtain ⟨w, hw⟩ :=
      BillingMahlerField.descentElement_eq_epsilon_mul_integral_sq_of_ideal_square
        x z I hideal hnonsquare hnorm
    obtain ⟨a, b, c, habc⟩ :=
      BillingMahlerField.ringOfIntegers_exists_thetaBasis_coords
        (BillingMahlerField.epsilonInteger * w)
    have hsquare :
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
          BillingMahlerField.thetaBasisElement a b c ^ 2 := by
      calc
        BillingMahlerField.epsilon * BillingMahlerField.descentElement x z =
            BillingMahlerField.epsilon *
              (BillingMahlerField.epsilon * (w : BillingMahlerField.K) ^ 2) := by
                rw [hw]
        _ = (((BillingMahlerField.epsilonInteger * w :
              NumberField.RingOfIntegers BillingMahlerField.K) :
                BillingMahlerField.K)) ^ 2 := by
              simp
              ring
        _ = BillingMahlerField.thetaBasisElement a b c ^ 2 := by rw [habc]
    have hcoeff :=
      BillingMahlerField.coefficient_system_of_epsilon_mul_descentElement_eq_sq
        x z a b c hsquare
    exact Or.inr ⟨x, z, a, b, c, hcop, hcoeff.1, hcoeff.2.1, hcoeff.2.2⟩

/-- Every rational affine point on `11a3` is one of its four affine cusps. -/
theorem E11_rational_points_boundary
    {X Y : ℚ} (hcurve : RationalPointsN11.E11AffineEquation X Y) :
    RationalPointsN11.E11DegenerateParameter X := by
  have hmordell : RationalPointsN11Descent.MordellEquation
      (9 * X + 24) (27 * Y) :=
    RationalPointsN11Descent.mordellEquation_of_E11 hcurve
  rcases billing_mahler_rational_point_dichotomy hmordell with hexceptional | hordinary
  · obtain ⟨x, y, hx, _hy, hyDiscr⟩ := hexceptional
    have hxBoundary : x = -12 ∨ x = 24 :=
      RationalPointsN11Descent.exceptional_integral_point_boundary x y
        (by
          have := hmordell
          rw [hx, _hy] at this
          have hrat : (y : ℚ) ^ 2 =
              (x : ℚ) ^ 3 - 432 * (x : ℚ) + 8208 := by
            simpa [RationalPointsN11Descent.MordellEquation] using this
          exact_mod_cast hrat)
        hyDiscr
    unfold RationalPointsN11.E11DegenerateParameter
    rcases hxBoundary with rfl | rfl
    · right
      norm_num at hx
      linarith
    · left
      norm_num at hx
      linarith
  · obtain ⟨x, z, a, b, c, hcop, hfirst, hmid, hthird⟩ := hordinary
    exact (RationalPointsN11Descent.no_billing_mahler_coefficient_system
      x z a b c hcop hfirst hmid hthird).elim

end CyclicExclusion11

end MazurProof

end

theorem solution
    {X Y : ℚ} (h : Y ^ 2 = X ^ 3 + 8 * X ^ 2 + 16 * X + 16) : X = 0 ∨ X = -4 :=
  MazurProof.CyclicExclusion11.E11_rational_points_boundary h
