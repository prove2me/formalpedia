-- Prove2me | solution 1 for MazurHuang.exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:14:48.936019+00:00
-- url     : https://prove2.me/submissions/f12f3cc3-7316-4528-a337-23b84687240c

/-
Rational points of orders 5 and 7 give a rational point of the fibre product X_0(5) x_j X_0(7).

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
  * scratch/TateZ2xZ10Reduction.lean lines 73-100 (the Tate normal form curve)
  * FLT/Assumptions/MazurProof/TateNormalFormBridge.lean lines 13-32 (the marked origin) and the bridge statement with the j-invariant, taken
    from the published theorem MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three
  * FLT/Assumptions/MazurProof/TateOriginDivision.lean lines 20-171 (division polynomials at the Tate origin for odd orders)
  * FLT/Assumptions/MazurProof/TorsionDefs.lean (HasRationalPointOfOrder)
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (J5Numerator, J7Numerator, X035FiberEquation)
  * FLT/Assumptions/MazurProof/CyclicExclusion35.lean (the Tate parameters of orders 5 and 7, their discriminants and j-invariants,
    simultaneous_orders_five_seven_to_X035_fiber)
  * the published statement
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_MazurHuang_exists_tate_normal_form_with_j_of_addOrderOf_gt_three

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

/- Source: flt@51bbb4f191ad scratch/TateZ2xZ10Reduction.lean, lines 73-100. -/
section

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

end

end Scratch.TateZ2xZ10Reduction

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TateNormalFormBridge.lean, lines 13-32. -/
section

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

/-- The Tate-normal-form bridge with the order, the nonvanishing of `b` and the `j`-invariant
(statement as in `FLT/Assumptions/MazurProof/TateNormalFormBridge.lean`), here obtained from the
published theorem `MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three`, which states
the same fact with the curve and the marked point written out. -/
theorem exists_tate_normalized_of_addOrder_gt_three_with_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          (tateNormalFormCurve b c).j = E.j := by
  obtain ⟨b, c, hb, hEll, hj, _h, hord⟩ :=
    MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three E P n hn hP
  exact ⟨b, c, hEll, hord, hb, hj⟩

end

end MazurProof.TateNormalFormBridge

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TateOriginDivision.lean. -/
section

-- FLT/Assumptions/MazurProof/TateOriginDivision.lean, lines 20-170
open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision

open Scratch.TateZ2xZ10Reduction

noncomputable section

abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

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

theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]

/-- The marked point `(0,0)` on a Tate normal form. -/
def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

theorem tateOrigin_eq_normalized_origin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateNormalFormBridge.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-- For odd `n`, vanishing of the `n`-multiple of the Tate origin implies the
raw division condition `preΨ'_n(0) = 0`. -/
theorem prePsi_eval_zero_of_odd_nsmul_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hn : n • tateOrigin b c = 0) :
    ((W b c).preΨ' n).eval 0 = 0 := by
  have hPsiSq : ((W b c).ΨSq (n : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp hn
  change ((W b c).ΨSq n).eval 0 = 0 at hPsiSq
  rw [(W b c).ΨSq_ofNat n] at hPsiSq
  simpa [hnodd] using hPsiSq

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

/-- The raw odd division polynomial vanishes at a Tate origin of exact order
`n`. -/
theorem prePsi_eval_zero_of_odd_addOrder
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' n).eval 0 = 0 := by
  apply prePsi_eval_zero_of_odd_nsmul_eq_zero b c hnodd
  simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)

/-- Every positive proper odd multiple below an exact order has nonzero raw
division evaluation. -/
theorem prePsi_eval_ne_zero_of_lt_addOrder
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {m n : ℕ} (hnpos : 0 < n) (hmpos : 0 < m) (hmn : m < n)
    (hmodd : ¬ Even m) (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' m).eval 0 ≠ 0 := by
  have hm : m • tateOrigin b c ≠ 0 :=
    ((addOrderOf_eq_iff (x := tateOrigin b c) hnpos).mp hord).2 m hmn hmpos
  exact prePsi_eval_ne_zero_of_odd_nsmul_ne_zero b c hmodd hm


end

end MazurProof.TateOriginDivision

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TorsionDefs.lean (whole module, imports dropped). -/
section

/-!
# Torsion definitions for the Mazur bound proof

Extracted from Axioms.lean to break import cycles.
Both Axioms.lean and RealTorsionBound.lean import this file.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

end MazurProof

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 23-32
/-- The standard `X₀(5)` numerator in its Hauptmodul `a`. -/
def J5Numerator (a : ℚ) : ℚ := (a ^ 2 + 10 * a + 5) ^ 3

/-- The standard `X₀(7)` numerator in its Hauptmodul `b`. -/
def J7Numerator (b : ℚ) : ℚ :=
  (b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3

/-- The affine fiber product `X₀(5) ×_j X₀(7)`. -/
def X035FiberEquation (a b : ℚ) : Prop :=
  b * J5Numerator a = a * J7Numerator b


end

end MazurProof.RationalPointsX135

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/CyclicExclusion35.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof

open Polynomial
open Scratch.TateZ2xZ10Reduction

noncomputable section

-- FLT/Assumptions/MazurProof/CyclicExclusion35.lean, lines 63-301
private abbrev TateCurve35 (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

private lemma eval_prePsi_five_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 5).eval 0 =
      ((TateCurve35 b c).preΨ₄).eval 0 *
          ((TateCurve35 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((TateCurve35 b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0)
    ((TateCurve35 b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_seven_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 7).eval 0 =
      ((TateCurve35 b c).preΨ' 5).eval 0 *
          (((TateCurve35 b c).preΨ' 3).eval 0) ^ 3 -
        ((TateCurve35 b c).preΨ' 4).eval 0 ^ 3 *
          ((TateCurve35 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0)
    ((TateCurve35 b c).preΨ'_odd 1)
  simpa using h

private theorem prePsi_five_at_origin_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 5).eval 0 = b ^ 8 * (b - c) := by
  rw [eval_prePsi_five_35]
  simp [TateCurve35, tateNormalFormCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem prePsi_seven_at_origin_35 (b c : ℚ) :
    ((TateCurve35 b c).preΨ' 7).eval 0 =
      b ^ 16 * (c ^ 3 - b ^ 2 + b * c) := by
  rw [eval_prePsi_seven_35, eval_prePsi_five_35]
  simp [TateCurve35, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem order_five_parameter_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 b c)]
    (hb : b ≠ 0)
    (hord : addOrderOf (TateNormalFormBridge.tateOrigin b c) = 5) :
    c = b := by
  have hord' : addOrderOf (TateOriginDivision.tateOrigin b c) = 5 := by
    rw [TateOriginDivision.tateOrigin_eq_normalized_origin]
    exact hord
  have hpre := TateOriginDivision.prePsi_eval_zero_of_odd_addOrder
    b c (show ¬ Even 5 by decide) hord'
  rw [prePsi_five_at_origin_35] at hpre
  have : b - c = 0 :=
    (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 8 hb)
  linarith

private theorem order_seven_parameter_eq
    (b c : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 b c)]
    (hb : b ≠ 0)
    (hord : addOrderOf (TateNormalFormBridge.tateOrigin b c) = 7) :
    c ^ 3 - b ^ 2 + b * c = 0 := by
  have hord' : addOrderOf (TateOriginDivision.tateOrigin b c) = 7 := by
    rw [TateOriginDivision.tateOrigin_eq_normalized_origin]
    exact hord
  have hpre := TateOriginDivision.prePsi_eval_zero_of_odd_addOrder
    b c (show ¬ Even 7 by decide) hord'
  rw [prePsi_seven_at_origin_35] at hpre
  exact (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 16 hb)

private def hauptmodul5 (p : ℚ) : ℚ :=
  (p ^ 2 - 11 * p - 1) / p

private def hauptmodul7 (t : ℚ) : ℚ :=
  (t ^ 3 - 8 * t ^ 2 + 5 * t + 1) / (t * (t - 1))

private theorem tate_order_five_delta (p : ℚ) :
    (TateCurve35 p p).Δ = p ^ 5 * (p ^ 2 - 11 * p - 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private theorem tate_order_five_c4 (p : ℚ) :
    (TateCurve35 p p).c₄ =
      p ^ 4 - 12 * p ^ 3 + 14 * p ^ 2 + 12 * p + 1 := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem tate_order_seven_delta (t : ℚ) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).Δ =
      t ^ 7 * (t - 1) ^ 7 *
        (t ^ 3 - 8 * t ^ 2 + 5 * t + 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private theorem tate_order_seven_c4 (t : ℚ) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).c₄ =
      (t ^ 2 - t + 1) *
        (t ^ 6 - 11 * t ^ 5 + 30 * t ^ 4 - 15 * t ^ 3 -
          10 * t ^ 2 + 5 * t + 1) := by
  simp [TateCurve35, tateNormalFormCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

private theorem tate_order_five_j
    (p : ℚ) [WeierstrassCurve.IsElliptic (TateCurve35 p p)]
    (hp : p ≠ 0) (hd : p ^ 2 - 11 * p - 1 ≠ 0) :
    (TateCurve35 p p).j =
      RationalPointsX135.J5Numerator (hauptmodul5 p) / hauptmodul5 p := by
  rw [WeierstrassCurve.j]
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  rw [tate_order_five_delta, tate_order_five_c4]
  unfold RationalPointsX135.J5Numerator hauptmodul5
  field_simp [hp, hd]
  ring

private theorem tate_order_seven_j
    (t : ℚ)
    [WeierstrassCurve.IsElliptic
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1)))]
    (ht : t ≠ 0) (ht1 : t - 1 ≠ 0)
    (hq : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0) :
    (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j =
      RationalPointsX135.J7Numerator (hauptmodul7 t) / hauptmodul7 t := by
  rw [WeierstrassCurve.j]
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  rw [tate_order_seven_delta, tate_order_seven_c4]
  unfold RationalPointsX135.J7Numerator hauptmodul7
  field_simp [ht, ht1, hq]
  ring

/-- Simultaneous rational points of orders five and seven give a noncuspidal
point on the affine fiber product `X₀(5) ×_j X₀(7)`. -/
theorem simultaneous_orders_five_seven_to_X035_fiber
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h5 : HasRationalPointOfOrder E 5)
    (h7 : HasRationalPointOfOrder E 7) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧
      RationalPointsX135.X035FiberEquation a b := by
  obtain ⟨P5, hP5⟩ := h5
  obtain ⟨p, c5, hEll5, hord5, hp, hj5⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three_with_j
      E P5 5 (by norm_num) hP5
  letI : WeierstrassCurve.IsElliptic (TateCurve35 p c5) := hEll5
  have hc5 : c5 = p := order_five_parameter_eq p c5 hp hord5
  subst c5
  have hd5 : p ^ 2 - 11 * p - 1 ≠ 0 := by
    intro hd
    have hDelta : (TateCurve35 p p).Δ ≠ 0 :=
      (TateCurve35 p p).isUnit_Δ.ne_zero
    apply hDelta
    rw [tate_order_five_delta, hd]
    ring
  let a : ℚ := hauptmodul5 p
  have ha : a ≠ 0 := by
    exact div_ne_zero hd5 hp
  have hj5formula : (TateCurve35 p p).j =
      RationalPointsX135.J5Numerator a / a := by
    exact tate_order_five_j p hp hd5

  obtain ⟨P7, hP7⟩ := h7
  obtain ⟨b7, c7, hEll7, hord7, hb7, hj7⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three_with_j
      E P7 7 (by norm_num) hP7
  letI : WeierstrassCurve.IsElliptic (TateCurve35 b7 c7) := hEll7
  have hF7 : c7 ^ 3 - b7 ^ 2 + b7 * c7 = 0 :=
    order_seven_parameter_eq b7 c7 hb7 hord7
  have hc7 : c7 ≠ 0 := by
    intro hc
    rw [hc] at hF7
    norm_num at hF7
    exact hb7 hF7
  let t : ℚ := b7 / c7
  have hb7tc : b7 = t * c7 := by
    dsimp [t]
    field_simp [hc7]
  have hc7param : c7 = t * (t - 1) := by
    have hc7sq : c7 ^ 2 ≠ 0 := pow_ne_zero 2 hc7
    have hfactor : c7 ^ 2 * (c7 - t ^ 2 + t) = 0 := by
      rw [hb7tc] at hF7
      linear_combination hF7
    have hlinear := (mul_eq_zero.mp hfactor).resolve_left hc7sq
    nlinarith
  have hb7param : b7 = t ^ 2 * (t - 1) := by
    rw [hb7tc, hc7param]
    ring
  have ht : t ≠ 0 := by
    intro ht
    apply hb7
    rw [hb7param, ht]
    ring
  have ht1 : t - 1 ≠ 0 := by
    intro ht1
    apply hb7
    rw [hb7param, ht1]
    ring
  have hcurve7 : TateCurve35 b7 c7 =
      TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1)) := by
    rw [hb7param, hc7param]
  letI hEll7' : WeierstrassCurve.IsElliptic
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))) := by
    rw [← hcurve7]
    exact hEll7
  have hq7 : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0 := by
    intro hq
    have hDelta :
        (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).Δ ≠ 0 :=
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).isUnit_Δ.ne_zero
    apply hDelta
    rw [tate_order_seven_delta, hq]
    ring
  let b : ℚ := hauptmodul7 t
  have hb : b ≠ 0 := by
    exact div_ne_zero hq7 (mul_ne_zero ht ht1)
  have hj7' :
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j = E.j := by
    simpa only [hcurve7] using hj7
  have hj7formula :
      (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j =
        RationalPointsX135.J7Numerator b / b := by
    exact tate_order_seven_j t ht ht1 hq7
  have hj : RationalPointsX135.J5Numerator a / a =
      RationalPointsX135.J7Numerator b / b := by
    calc
      RationalPointsX135.J5Numerator a / a = (TateCurve35 p p).j :=
        hj5formula.symm
      _ = E.j := hj5
      _ = (TateCurve35 (t ^ 2 * (t - 1)) (t * (t - 1))).j := hj7'.symm
      _ = RationalPointsX135.J7Numerator b / b := hj7formula
  refine ⟨a, b, ha, hb, ?_⟩
  unfold RationalPointsX135.X035FiberEquation
  field_simp [ha, hb] at hj
  simpa [mul_comm] using hj


end

end MazurProof

end

open scoped WeierstrassCurve.Affine

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P Q : (E⁄ℚ).Point)
    (hP : addOrderOf P = 5) (hQ : addOrderOf Q = 7) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧
      b * (a ^ 2 + 10 * a + 5) ^ 3 = a * ((b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3) :=
  MazurProof.simultaneous_orders_five_seven_to_X035_fiber E ⟨P, hP⟩ ⟨Q, hQ⟩
