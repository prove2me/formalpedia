-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:17:28.930578+00:00
-- url     : https://prove2.me/submissions/837ab803-9a0a-4c29-b56f-efea3b295694

/-
The dual 3-isogeny after the 3-isogeny is multiplication by 3.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (nonvanishing lemmas, tangent and chord formulas on the short model, dual_three_comp_x,
    dual_comp_threeIsogenyPoint; the y-coordinate identity is taken from the published theorem)
  * division-polynomial interface derived from three Proved platform theorems (glue)
  * FLT/Assumptions/MazurProof/TateOriginDivision.lean (psi_ne_zero_rat, nsmul_eq_zero_iff_PsiSq_eval; used for the points with x = 0)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_Y_eq_tripleY

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

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TateOriginDivision.lean. -/
section

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision

noncomputable section

-- FLT/Assumptions/MazurProof/TateOriginDivision.lean, lines 32-101
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
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _


end

end MazurProof.TateOriginDivision

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

open MazurHuang.ThreeIsogeny35

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 792-870
private theorem dual_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnE35Dual s t) : s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnE35Dual] at h
  nlinarith [sq_nonneg t]

private theorem shortCubic_ne_zero (x : ℚ) :
    x ^ 3 + 16 * x ^ 2 + 224 * x + 784 ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 3 + C 16 * X ^ 2 + C 224 * X + C 784
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    norm_cast
  obtain ⟨z, hx, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hx] at h
  have hz : z ^ 3 + 16 * z ^ 2 + 224 * z + 784 = 0 := by
    have hzcast : ((z ^ 3 + 16 * z ^ 2 + 224 * z + 784 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 3) ^ 3 + 16 * (z : ZMod 3) ^ 2 +
      224 * (z : ZMod 3) + 784 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 3)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ u : ZMod 3,
    u ^ 3 + 16 * u ^ 2 + 224 * u + 784 ≠ 0) (z : ZMod 3) hzmod

private theorem short_y_ne_zero {x y : ℚ} (h : OnE35Short x y) : y ≠ 0 := by
  intro hy
  apply shortCubic_ne_zero x
  unfold OnE35Short at h
  rw [hy] at h
  norm_num at h
  linear_combination -h

private theorem short_three_nsmul_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hx : x = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval E35ShortCurve h).mpr
  rw [E35ShortCurve.ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E35ShortCurve, hx]
  norm_num

private theorem short_three_x_factor_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    (3 * x + 28) * (x ^ 2 + 12 * x + 336) ≠ 0 := by
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hlin
    have hxval : x = -28 / 3 := by linarith
    rw [hxval] at h
    norm_num [OnE35Short] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero hlin hquad

private theorem threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : threeIsogenyX x ≠ 0 := by
  have hfac := short_three_x_factor_ne_zero hx h
  unfold threeIsogenyX
  apply div_ne_zero
  · have hid :
        9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224 =
          3 * (3 * x + 28) * (x ^ 2 + 12 * x + 336) := by ring
    rw [hid]
    simpa [mul_assoc] using
      mul_ne_zero (show (3 : ℚ) ≠ 0 by norm_num) hfac
  · exact pow_ne_zero 2 hx

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 912-914
@[simp] theorem E35ShortCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY E35ShortCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, E35ShortCurve]

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 935-1030
private theorem E35ShortCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope E35ShortCurve x x y y = shortTangent x y := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E35ShortCurve x y := by
    rw [E35ShortCurve_negY]
    intro h
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [E35ShortCurve, shortTangent, WeierstrassCurve.Affine.negY]
  ring

private theorem E35ShortCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX E35ShortCurve x x (shortTangent x y) =
      shortDoubleX x y := by
  simp [E35ShortCurve, shortDoubleX]
  ring

private theorem E35ShortCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY E35ShortCurve x x y (shortTangent x y) =
      shortDoubleY x y := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E35ShortCurve shortDoubleY shortDoubleX
  ring

private theorem E35ShortCurve_slope_double {x y : ℚ}
    (hxx : shortDoubleX x y ≠ x) :
    WeierstrassCurve.Affine.slope E35ShortCurve
        (shortDoubleX x y) x (shortDoubleY x y) y =
      shortTripleSlope x y := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxx]
  rfl

private theorem E35ShortCurve_addX_double (x y : ℚ) :
    WeierstrassCurve.Affine.addX E35ShortCurve
        (shortDoubleX x y) x (shortTripleSlope x y) =
      shortTripleX x y := by
  simp [E35ShortCurve, shortTripleX]

private theorem E35ShortCurve_addY_double (x y : ℚ) :
    WeierstrassCurve.Affine.addY E35ShortCurve
        (shortDoubleX x y) x (shortDoubleY x y) (shortTripleSlope x y) =
      shortTripleY x y := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E35ShortCurve shortTripleY shortTripleX
  ring

private theorem shortDoubleX_sub_identity {x y : ℚ} (hy : y ≠ 0)
    (h : OnE35Short x y) :
    4 * y ^ 2 * (shortDoubleX x y - x) =
      -x * (3 * x + 28) * (x ^ 2 + 12 * x + 336) := by
  unfold shortDoubleX shortTangent
  unfold OnE35Short at h
  field_simp [hy]
  rw [h]
  ring

private theorem shortDoubleX_ne_self {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : shortDoubleX x y ≠ x := by
  have hy := short_y_ne_zero h
  have hid := shortDoubleX_sub_identity hy h
  have hfac := short_three_x_factor_ne_zero hx h
  intro heq
  rw [heq, sub_self, mul_zero] at hid
  have hnonzero : -x * ((3 * x + 28) * (x ^ 2 + 12 * x + 336)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hx) hfac
  apply hnonzero
  simpa [mul_assoc] using hid.symm

private theorem dual_three_comp_x {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyX (threeIsogenyX x) = shortTripleX x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyX shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX shortDoubleY shortDoubleX shortTangent
  unfold OnE35Short at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [h, hy4, hy6, hy8]
  ring

/-- The y-coordinate of the composition (statement as in
`FLT/Assumptions/MazurProof/RationalPointsX135.lean`), here the published theorem
`MazurHuang.threeIsogeny35_dual_comp_Y_eq_tripleY`. -/
private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      shortTripleY x y :=
  MazurHuang.threeIsogeny35_dual_comp_Y_eq_tripleY hx h

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 1068-1118
set_option maxHeartbeats 0 in
/-- The explicit dual isogeny composed with the explicit three-isogeny is
multiplication by three on the short model. -/
theorem dual_comp_threeIsogenyPoint (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hzero : threeIsogenyPoint
            (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) =
            (0 : E35DualPoint) := by
          simp only [threeIsogenyPoint]
          rw [dif_pos hx]
          change (0 : E35DualPoint) = (0 : E35DualPoint)
          rfl
        rw [hzero, dualThreeIsogenyPoint_zero]
        exact (short_three_nsmul_of_x_zero h hx).symm
      · rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
        have hphi := threeIsogenyX_ne_zero hx hcurve
        change dualThreeIsogenyPoint
            (.some (threeIsogenyX x) (threeIsogenyY x y) _) = _
        rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
        have hy := short_y_ne_zero hcurve
        have hneg : y ≠ WeierstrassCurve.Affine.negY E35ShortCurve x y := by
          rw [E35ShortCurve_negY]
          intro heq
          apply hy
          linarith
        have hxx := shortDoubleX_ne_self hx hcurve
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
          two_nsmul]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by
          rw [E35ShortCurve_slope_self hy, E35ShortCurve_addX_tangent]
          exact hxx)]
        change WeierstrassCurve.Affine.Point.some
            (dualThreeIsogenyX (threeIsogenyX x))
            (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) _ = _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · rw [E35ShortCurve_slope_self hy,
            E35ShortCurve_addX_tangent, E35ShortCurve_addY_tangent,
            E35ShortCurve_slope_double hxx, E35ShortCurve_addX_double]
          exact dual_three_comp_x hx hcurve
        · rw [E35ShortCurve_slope_self hy,
            E35ShortCurve_addX_tangent, E35ShortCurve_addY_tangent,
            E35ShortCurve_slope_double hxx,
            E35ShortCurve_addY_double]
          exact dual_three_comp_y hx hcurve


end

end MazurProof.RationalPointsX135

end

open MazurHuang.ThreeIsogeny35

theorem solution
    (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P :=
  MazurProof.RationalPointsX135.dual_comp_threeIsogenyPoint P
