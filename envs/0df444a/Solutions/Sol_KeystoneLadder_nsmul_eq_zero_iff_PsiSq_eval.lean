-- Prove2me | solution 1 for KeystoneLadder.nsmul_eq_zero_iff_PsiSq_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:41.167674+00:00
-- url     : https://prove2.me/submissions/fd3920f8-a831-4b86-b18c-0e914e81fd7a

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneLadder
import Definitions.Def_PsiInvariant
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
import Theorems.Thm_KeystoneLadder_SameP1Vec_second_eq_zero_of_same_infty
import Theorems.Thm_KeystoneLadder_SameP1Vec_second_ne_zero_of_same_affine
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_three
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_four
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_correct_seam
import Theorems.Thm_KeystoneLadder_xLadderPair_same_xPair_EDS
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Definitions.Def_KeystoneDoubling

/-! Proofs of the lemmas stated in `Theorems.Thm_DivisionPolynomial_XPairEDS` and their helpers. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

open scoped Classical

variable {k : Type*} [Field k]

namespace KeystoneLadder

open XOnly

/-- Missing Mathlib/repo EDS fact: for an elliptic curve, the univariate division-polynomial
representative has no zero-vector specialization and agrees with the corrected Montgomery-pair
ladder.  The first conjunct is the no-common-root/coprimality statement for `Φₙ` and `ΨSqₙ`;
the second conjunct is the EDS recurrence compatibility with `doubleVec` and `diffAddOrInfVec`. -/
public theorem xPair_ne_zero_and_same_xLadderRep_EDS
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
      xPair W (n : ℤ) x ≠ 0 ∧
      SameP1Vec
        (XOnly.xLadderRep (E := W⁄k) x n)
        (xPair W (n : ℤ) x) := by
    have h := xLadderPair_same_xPair_EDS (W := W) n x h4 hψ_ne hc3
    exact ⟨h.1, by simpa [XOnly.xLadderRep] using h.2.2.1⟩

/-- Irreducible remaining EDS recurrence seam: the corrected Montgomery-pair ladder agrees
with the `[Φₙ, ΨSqₙ]` division-polynomial representative. -/
public theorem xPair_same_xLadderRep_seam_EDS_core
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x n)
      (xPair W (n : ℤ) x) :=
  (xPair_ne_zero_and_same_xLadderRep_EDS (W := W) n x h4 hψ_ne hc3).2

/-- SEAM: the EDS/division-polynomial compatibility of the raw x-only ladder. -/
public theorem xPair_same_xLadderRep_seam
    (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (XOnly.xLadderRep (E := W⁄k) x n)
      (xPair W (n : ℤ) x) :=
  xPair_same_xLadderRep_seam_EDS_core (W := W) n x h4 hψ_ne hc3

/-- The projective division-polynomial coordinate formula assembled from the ladder seams. -/
public theorem xRep_nsmul_same_xPair (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : (W⁄k).Point)).xRep)
      (xPair W (n : ℤ) x) := by
  exact SameP1Vec.trans
    (XOnly.xLadderRep_correct_seam (E := W⁄k) h n)
    (xPair_same_xLadderRep_seam (W := W) n x h4 hψ_ne hc3)

/-- Keystone target reduced to the projective division-polynomial coordinate formula. -/
theorem _root_.solution (W : WeierstrassCurve k) [W.IsElliptic]
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
