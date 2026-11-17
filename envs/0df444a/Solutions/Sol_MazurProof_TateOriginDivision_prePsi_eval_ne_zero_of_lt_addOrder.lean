-- Prove2me | solution 1 for MazurProof.TateOriginDivision.prePsi_eval_ne_zero_of_lt_addOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:06:05.787305+00:00
-- url     : https://prove2.me/submissions/5ae055e4-2608-461a-93d6-b857560cc8be

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateNormalFormBridge
import Definitions.Def_TateOriginDivision
import Definitions.Def_TateZ2xZ10Reduction
import Definitions.Def_TorsionDefs
import Theorems.Thm_KeystoneLadder_nsmul_eq_zero_iff_PsiSq_eval
import Definitions.Def_KeystoneLadder
import Definitions.Def_PsiInvariant
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_three
import Theorems.Thm_KeystoneLadder_XOnly_xLadderRep_four

/-! Proofs of the lemmas stated in `Theorems.Thm_TateNormalForm_OddOrderDivision` and their helpers. -/

open Polynomial

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision

open Scratch.TateZ2xZ10Reduction

noncomputable section

theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
        (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsi_ne : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsi_deg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree
            ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
              (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hPsi :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hPsi (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne n (by intro h; exact hm (by simp [h])))
      (hPsi_deg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne _ (Nat.succ_ne_zero n))
      (hPsi_deg _ (Nat.succ_ne_zero n))

theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    n • (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hc3 : W.Ψ₃ ≠ 0 :=
    WeierstrassCurve.Ψ₃_ne_zero W (by norm_num)
  have key := KeystoneLadder.nsmul_eq_zero_iff_PsiSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _

/-- For odd `n`, a nonzero `n`-multiple forces the raw division evaluation to
be nonzero. -/
theorem prePsi_eval_ne_zero_of_odd_nsmul_ne_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hn : n • tateOrigin b c ≠ 0) :
    ((W b c).preΨ' n).eval 0 ≠ 0 := by
  intro hpre
  apply hn
  apply (nsmul_eq_zero_iff_PsiSq_eval (W b c)
    (tate_origin_nonsingular b c)).mpr
  rw [(W b c).ΨSq_ofNat n]
  simp [hnodd, hpre]

/-- Every positive proper odd multiple below an exact order has nonzero raw
division evaluation. -/
theorem _root_.solution
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {m n : ℕ} (hnpos : 0 < n) (hmpos : 0 < m) (hmn : m < n)
    (hmodd : ¬ Even m) (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' m).eval 0 ≠ 0 := by
  have hm : m • tateOrigin b c ≠ 0 :=
    ((addOrderOf_eq_iff (x := tateOrigin b c) hnpos).mp hord).2 m hmn hmpos
  exact prePsi_eval_ne_zero_of_odd_nsmul_ne_zero b c hmodd hm

end

end MazurProof.TateOriginDivision
