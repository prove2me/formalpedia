-- Prove2me | solution 1 for KeystoneLadder.SameP1Vec.trans
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:17.013904+00:00
-- url     : https://prove2.me/submissions/1cbc2166-ebe7-4b18-a0dd-1d857b594cb4

import Mathlib
import Definitions.Def_KeystoneLadder

/-! Proofs of the lemmas stated in `Theorems.Thm_XOnlyLadder` and their helpers. -/
set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedTactic false

set_option linter.overlappingInstances false

open Polynomial

open WeierstrassCurve

open WeierstrassCurve.Affine

noncomputable section

namespace KeystoneLadder

universe u

variable {k : Type u} [Field k] [DecidableEq k]

namespace P1

variable [Field k]

@[simp] public lemma same_refl (A : P1 k) : Same A A := by
  dsimp [Same]

@[simp] public lemma same_mk_iff {A B : P1 k} :
    Same A B ↔ A.X * B.Z = B.X * A.Z := Iff.rfl

end P1

variable (E : WeierstrassCurve k)

@[simp] public lemma xRep_zero :
    xRep E (0 : E.toAffine.Point) = xInf := rfl

@[simp] public lemma xRep_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    xRep E (Point.some x y h : E.toAffine.Point) = xAff x := rfl

@[simp] public lemma xRep_some_X {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).X = x := rfl

@[simp] public lemma xRep_some_Z {x y : k} (h : E.toAffine.Nonsingular x y) :
    (xRep E (Point.some x y h : E.toAffine.Point)).Z = 1 := rfl

@[simp] public lemma xInf_X : (xInf : P1 k).X = 1 := rfl
@[simp] public lemma xInf_Z : (xInf : P1 k).Z = 0 := rfl
@[simp] public lemma xAff_X (x : k) : (xAff x).X = x := rfl
@[simp] public lemma xAff_Z (x : k) : (xAff x).Z = 1 := rfl

@[simp] public lemma xRep_neg_some_same {x y : k} (h : E.toAffine.Nonsingular x y) :
    P1.Same
      (xRep E (-(Point.some x y h : E.toAffine.Point)))
      (xRep E (Point.some x y h : E.toAffine.Point)) := by
  simp [xRep, xAff, P1.Same]

@[simp] public lemma xRep_add_some_of_X_ne
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep E
      ((Point.some x₁ y₁ h₁ : E.toAffine.Point) + Point.some x₂ y₂ h₂)
      = xAff (E.toAffine.addX x₁ x₂ (E.toAffine.slope x₁ x₂ y₁ y₂)) := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := E.toAffine) hx]
  rfl

@[simp] public lemma xRep_sub_some_of_X_ne
    {x₁ y₁ x₂ y₂ : k}
    {h₁ : E.toAffine.Nonsingular x₁ y₁}
    {h₂ : E.toAffine.Nonsingular x₂ y₂}
    (hx : x₁ ≠ x₂) :
    xRep E
      ((Point.some x₁ y₁ h₁ : E.toAffine.Point) - Point.some x₂ y₂ h₂)
      = xAff (E.toAffine.addX x₁ x₂
          (E.toAffine.slope x₁ x₂ y₁ (E.toAffine.negY x₂ y₂))) := by
  rw [sub_eq_add_neg]
  rw [WeierstrassCurve.Affine.Point.neg_some (W' := E.toAffine) h₂]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne (W := E.toAffine) hx]
  rfl

@[simp] public lemma p1_toVec_xInf :
    P1.toVec (xInf : P1 k) = ![1, 0] := rfl

@[simp] public lemma p1_toVec_xAff (x : k) :
    P1.toVec (xAff x : P1 k) = ![x, 1] := rfl

namespace SameP1Vec

theorem _root_.solution {u v w : Fin 2 → k} (huv : SameP1Vec u v) (hvw : SameP1Vec v w) :
    SameP1Vec u w := by
  rcases huv with ⟨c, hc, rfl⟩
  rcases hvw with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

end SameP1Vec

namespace XOnly

@[simp] public lemma xLadderRep_zero (x : k) :
    xLadderRep E x 0 = xInfVec := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xLadderRep_one (x : k) :
    xLadderRep E x 1 = xAffVec x := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xLadderRep_two (x : k) :
    xLadderRep E x 2 = doubleVec E (xAffVec x) := by
  simp [xLadderRep, xLadderPair]

@[simp] public lemma xRep_X_eq_point_xRep_zero (P : E.toAffine.Point) :
    (xRep E P).X = P.xRep 0 := by
  cases P <;> rfl

@[simp] public lemma xRep_Z_eq_point_xRep_one (P : E.toAffine.Point) :
    (xRep E P).Z = P.xRep 1 := by
  cases P <;> rfl

end XOnly

end KeystoneLadder
