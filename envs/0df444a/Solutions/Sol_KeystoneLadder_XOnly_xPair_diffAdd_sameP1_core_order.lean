-- Prove2me | solution 1 for KeystoneLadder.XOnly.xPair_diffAdd_sameP1_core_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:07:39.090341+00:00
-- url     : https://prove2.me/submissions/77700904-35f1-45df-afd4-7e6f0508ba28

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDiffAddCert
import Definitions.Def_KeystoneDoubling
import Definitions.Def_KeystoneLadder
import Theorems.Thm_WeierstrassCurve_Phi_PsiSq_no_common_eval_zero_odd
import Definitions.Def_KeystoneCoprimality
import Definitions.Def_WardSomos
import Theorems.Thm_WeierstrassCurve_deltaP_eval
import Theorems.Thm_WeierstrassCurve_sumNumP_eval
import Theorems.Thm_WeierstrassCurve_diffAddNumP_eval
import Theorems.Thm_WeierstrassCurve_PsiSq_two_mul_add_one
import Theorems.Thm_WeierstrassCurve_diffAdd_projective_two_mul_add_one

/-! Proofs of the lemmas stated in `Theorems.Thm_XOnlyLadder_SameProjectivePoint` and their helpers. -/
open Polynomial WeierstrassCurve

open scoped Classical

namespace KeystoneLadder

variable {k : Type*} [Field k]

end KeystoneLadder

namespace KeystoneLadder

namespace XOnly

open Polynomial

variable {k : Type*} [Field k]

@[simp] public theorem xPair_one_X (W : WeierstrassCurve k) (x : k) :
    X (xPair W 1 x) = x := by
  simp [xPair, X]

@[simp] public theorem xPair_one_Z (W : WeierstrassCurve k) (x : k) :
    Z (xPair W 1 x) = 1 := by
  simp [xPair, Z]

/--
The certificate uses projective order `(m, m+1)`, while the ladder step below
uses vector order `(m+1, m)`.  Hence the minus sign.  The denominator bridges use
only the square, so the sign disappears there.
-/
public theorem deltaP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.deltaP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = - deltaVec (xPair W (m + 1) x) (xPair W m x) := by
  simp [WeierstrassCurve.deltaP, deltaVec, xPair, X, Z] <;> ring

/-- Evaluated projective denominator equals the ladder `deltaVec` square. -/
public theorem diffAddDenP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddDenP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
  simp [WeierstrassCurve.diffAddDenP, deltaP_eval_xPair_succ_left] <;> ring

/-- Evaluated projective numerator equals the `X` component of the ladder diff-add. -/
public theorem diffAddNumP_eval_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    ((WeierstrassCurve.diffAddNumP W
        (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = X (diffAddVec (E := W⁄k)
          (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
  simp only [WeierstrassCurve.diffAddNumP_eval, WeierstrassCurve.sumNumP_eval,
    WeierstrassCurve.deltaP_eval, diffAddVec, sumNumVec, deltaVec, xPair, X, Z,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, Algebra.algebraMap_self_apply,
    WeierstrassCurve.Φ_one, WeierstrassCurve.ΨSq_one, Polynomial.eval_X, Polynomial.eval_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Evaluated projective denominator equals the `Z` component of the ladder diff-add. -/
public theorem diffAddVec_Z_xPair_succ_left
    (W : WeierstrassCurve k) (m : ℤ) (x : k) :
    Z (diffAddVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      = ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  simp [WeierstrassCurve.diffAddDenP, WeierstrassCurve.deltaP,
    diffAddVec, deltaVec, xPair, X, Z] <;> ring

/-- Evaluated `PsiSq_two_mul_add_one`, in denominator form. -/
public theorem ΨSq_two_mul_add_one_eval_diffAddDenP
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    (W.ΨSq (2 * m + 1)).eval x
      = ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  have h := WeierstrassCurve.PsiSq_two_mul_add_one W m
  simpa using congrArg (fun p : Polynomial k => p.eval x) h

/-- Evaluated `PsiSq_two_mul_add_one`, directly in ladder-delta form. -/
public theorem ΨSq_two_mul_add_one_eval_deltaVec_sq
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    (W.ΨSq (2 * m + 1)).eval x
      = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
  calc
    (W.ΨSq (2 * m + 1)).eval x
        = ((WeierstrassCurve.diffAddDenP W
            (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
            exact ΨSq_two_mul_add_one_eval_diffAddDenP
              (W := W) (m := m) (x := x) h4 hψ_ne hc3
    _ = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
            rw [diffAddDenP_eval_xPair_succ_left]

/-- Evaluated projective diff-add certificate. -/
public theorem diffAdd_projective_two_mul_add_one_eval
    (W : WeierstrassCurve k) (m : ℤ) (x : k) (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    (W.Φ (2 * m + 1)).eval x *
        ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
      = (W.ΨSq (2 * m + 1)).eval x *
        ((WeierstrassCurve.diffAddNumP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
  have h := WeierstrassCurve.diffAdd_projective_two_mul_add_one W h4 hψ_ne hc3 m
  simpa using congrArg (fun p : Polynomial k => p.eval x) h

/--
The complete x-only diff-add wiring proof, with the one genuinely non-wiring
fact needed by the infinity branch isolated as `hΦinf`.

In the nonzero branch, scalar `1` works.  In the zero branch, the witness is
`(W.Φ (2*m+1)).eval x`, so `hΦinf` is exactly the required nonzero proof.
-/
public theorem xPair_diffAdd_sameP1_of_inf_phi_ne
    (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    (hΦinf :
      deltaVec (xPair W (m + 1) x) (xPair W m x) = 0 →
        (W.Φ (2 * m + 1)).eval x ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  by_cases hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0
  · simp only [diffAddOrInfVec, if_pos hδ]

    have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
      calc
        (W.ΨSq (2 * m + 1)).eval x
            = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 := by
                exact ΨSq_two_mul_add_one_eval_deltaVec_sq
                  (W := W) (m := m) (x := x) h4 hψ_ne hc3
        _ = 0 := by simp [hδ]

    refine ⟨(W.Φ (2 * m + 1)).eval x, hΦinf hδ, ?_⟩
    funext i
    fin_cases i <;> simp [xPair, xInfVec, hΨzero]

  · simp only [diffAddOrInfVec, if_neg hδ]

    have hΨDen :
        (W.ΨSq (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      exact ΨSq_two_mul_add_one_eval_diffAddDenP
        (W := W) (m := m) (x := x) h4 hψ_ne hc3

    have hDenNe :
        ((WeierstrassCurve.diffAddDenP W
          (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) ≠ 0 := by
      rw [diffAddDenP_eval_xPair_succ_left]
      exact pow_ne_zero 2 hδ

    have hProjEval :
        (W.Φ (2 * m + 1)).eval x *
            ((WeierstrassCurve.diffAddDenP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
          = (W.ΨSq (2 * m + 1)).eval x *
            ((WeierstrassCurve.diffAddNumP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      exact diffAdd_projective_two_mul_add_one_eval
        (W := W) (m := m) (x := x) h4 hψ_ne hc3

    have hΦNum :
        (W.Φ (2 * m + 1)).eval x
          = ((WeierstrassCurve.diffAddNumP W
              (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
      exact mul_right_cancel₀ hDenNe <| by
        calc
          (W.Φ (2 * m + 1)).eval x *
              ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x)
              = (W.ΨSq (2 * m + 1)).eval x *
                ((WeierstrassCurve.diffAddNumP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := hProjEval
          _ = ((WeierstrassCurve.diffAddDenP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) *
                ((WeierstrassCurve.diffAddNumP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
                rw [hΨDen]
          _ = ((WeierstrassCurve.diffAddNumP W
                (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) *
                ((WeierstrassCurve.diffAddDenP W
                  (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))).eval x) := by
                ring

    have hXcoord :
        (W.Φ (2 * m + 1)).eval x
          = X (diffAddVec (E := W⁄k)
              (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
      exact hΦNum.trans
        (diffAddNumP_eval_xPair_succ_left (W := W) (m := m) (x := x))

    have hZcoord :
        (W.ΨSq (2 * m + 1)).eval x
          = Z (diffAddVec (E := W⁄k)
              (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x)) := by
      exact hΨDen.trans
        (diffAddVec_Z_xPair_succ_left (W := W) (m := m) (x := x)).symm

    refine ⟨1, one_ne_zero, ?_⟩
    funext i
    fin_cases i
    · simpa [xPair, X, one_smul] using hXcoord
    · simpa [xPair, Z, one_smul] using hZcoord

public theorem xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    (hδ : deltaVec (xPair W (m + 1) x) (xPair W m x) = 0) :
    (W.Φ (2 * m + 1)).eval x ≠ 0 := by
  have hΨzero : (W.ΨSq (2 * m + 1)).eval x = 0 := by
    calc
      (W.ΨSq (2 * m + 1)).eval x
          = (deltaVec (xPair W (m + 1) x) (xPair W m x)) ^ 2 :=
            ΨSq_two_mul_add_one_eval_deltaVec_sq (W := W) (m := m) (x := x) h4 hψ_ne hc3
      _ = 0 := by simp [hδ]
  -- AVENUE (c): non-circular division-polynomial coprimality gcd(Φ_(2m+1), ΨSq_(2m+1)) = 1
  intro hΦ0
  exact WeierstrassCurve.Phi_PsiSq_no_common_eval_zero_odd (W := W) (x := x) h4 m ⟨hΦ0, hΨzero⟩

/-- Keystone x-only differential-addition wiring lemma. -/
public theorem xPair_diffAdd_sameP1
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W (m + 1) x) (xPair W m x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  refine xPair_diffAdd_sameP1_of_inf_phi_ne
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 ?_
  intro hδ
  exact xPair_odd_phi_eval_ne_zero_of_delta_zero
    (W := W) (m := m) (x := x) h4 hψ_ne hc3 hδ

/-- `diffAddOrInfVec` is symmetric in its first two (x-only) arguments: `sumNumVec` is
symmetric and `deltaVec` only enters squared / through its vanishing. -/
public theorem diffAddOrInfVec_comm (E : WeierstrassCurve k) (A B D : Fin 2 → k) :
    diffAddOrInfVec E A B D = diffAddOrInfVec E B A D := by
  have hδ : deltaVec A B = 0 ↔ deltaVec B A = 0 := by
    have : deltaVec A B = - deltaVec B A := by simp only [deltaVec]; ring
    rw [this, neg_eq_zero]
  unfold diffAddOrInfVec
  by_cases h : deltaVec A B = 0
  · rw [if_pos h, if_pos (hδ.mp h)]
  · rw [if_neg h, if_neg (fun hba => h (hδ.mpr hba))]
    funext i
    fin_cases i <;>
      simp only [diffAddVec, sumNumVec, deltaVec, X, Z, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- Core-order (A = xPair m, B = xPair (m+1)) differential-addition wiring, obtained from
`xPair_diffAdd_sameP1` by the symmetry above. -/
theorem _root_.solution
    (W : WeierstrassCurve k) [W.IsElliptic] (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec
      (diffAddOrInfVec (E := W⁄k)
        (xPair W m x) (xPair W (m + 1) x) (xPair W 1 x))
      (xPair W (2 * m + 1) x) := by
  rw [diffAddOrInfVec_comm]
  exact xPair_diffAdd_sameP1 (W := W) (m := m) (x := x) h4 hψ_ne hc3

end XOnly

end KeystoneLadder
