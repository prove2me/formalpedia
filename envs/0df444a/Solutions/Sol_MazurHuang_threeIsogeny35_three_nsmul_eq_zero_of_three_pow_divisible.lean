-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_three_nsmul_eq_zero_of_three_pow_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:20:53.652828+00:00
-- url     : https://prove2.me/submissions/6f2666ac-1f31-4a42-aa7a-c5047a12ed25

/-
3-adic filtration on y^2 = x^3 + (4x+28)^2: a point 3P divisible by all powers of 3 is zero.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (explicit tripling formulas, 3-adic valuations of their numerators and denominators, the
    formal kernel at 3 and its levels, reduction modulo 3, E35_three_nsmul_formal,
    E35_formal_separated; the composition of the two isogenies is taken from the published theorem)
  * the published statement, proved as E35_three_nsmul_eq_zero in the source
-/
import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35
import Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_eq_three_nsmul

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open MazurHuang.ThreeIsogeny35

/-- The explicit dual isogeny composed with the explicit three-isogeny is multiplication by three
(statement as in `FLT/Assumptions/MazurProof/RationalPointsX135.lean`), here the published theorem
`MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul`. -/
theorem dual_comp_threeIsogenyPoint (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P :=
  MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul P

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 9-883
def n35TripleDen (x : ℚ) : ℚ :=
  x * (3 * x + 28) * (x ^ 2 + 12 * x + 336)

def n35TripleXNum (x : ℚ) : ℚ :=
  x ^ 9 - 2688 * x ^ 7 - 103936 * x ^ 6 - 1204224 * x ^ 5 -
    4214784 * x ^ 4 + 119418880 * x ^ 3 + 1888223232 * x ^ 2 +
    13217562624 * x + 30840979456

def n35TripleYNum (x y : ℚ) : ℚ :=
  y * (x ^ 3 - 448 * x - 6272) *
    (x ^ 3 + 28 * x ^ 2 - 112 * x + 3136) *
    (x ^ 6 + 36 * x ^ 5 + 4480 * x ^ 4 + 82880 * x ^ 3 +
      878080 * x ^ 2 + 4566016 * x + 9834496)

private theorem n35TripleDen_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : n35TripleDen x ≠ 0 := by
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hlin
    have hxval : x = -28 / 3 := by linarith
    rw [hxval] at h
    norm_num [OnE35Short] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero (mul_ne_zero hx hlin) hquad

private theorem threeIsogenyX_eq_den (x : ℚ) (hx : x ≠ 0) :
    threeIsogenyX x = 3 * n35TripleDen x / x ^ 3 := by
  unfold threeIsogenyX n35TripleDen
  field_simp [hx]
  ring

private theorem threeIsogenyY_eq_factor (x y : ℚ) (hx : x ≠ 0) :
    threeIsogenyY x y = 27 * y * (x ^ 3 - 448 * x - 6272) / x ^ 3 := by
  unfold threeIsogenyY
  field_simp [hx]
  ring

set_option maxHeartbeats 0 in
private theorem n35TripleX_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyX (threeIsogenyX x) =
      n35TripleXNum x / n35TripleDen x ^ 2 := by
  have hd := n35TripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx]
  unfold dualThreeIsogenyX n35TripleXNum
  field_simp [hx, hd]
  unfold n35TripleDen
  ring

set_option maxHeartbeats 0 in
private theorem n35TripleY_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      n35TripleYNum x y / n35TripleDen x ^ 3 := by
  have hd := n35TripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx, threeIsogenyY_eq_factor x y hx]
  unfold dualThreeIsogenyY n35TripleYNum
  field_simp [hx, hd]
  unfold n35TripleDen
  ring

private theorem n35_val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 3 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.ofNat_zero_le _

private theorem n35_val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 3 a < padicValRat 3 b) :
    padicValRat 3 (a + b) = padicValRat 3 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by linarith
    have : padicValRat 3 b = padicValRat 3 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

private theorem n35_val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    l.sum = 0 ∨ padicValRat 3 q < padicValRat 3 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 3 q < padicValRat 3 a := hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 3 q < padicValRat 3 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

private theorem n35_val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    padicValRat 3 (q + l.sum) = padicValRat 3 q := by
  rcases n35_val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact n35_val_add_eq_left_of_lt hq hsum

private theorem n35_val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 3 x + (b : ℤ) * padicValRat 3 y ≤
      padicValRat 3 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow _, padicValRat.pow _]
  have hcval := n35_val_int_nonneg c
  omega

private theorem n35_val_x_monomial_ge
    {x : ℚ} (hx : x ≠ 0) (c : ℤ) (hc : c ≠ 0) (a : ℕ) :
    (a : ℤ) * padicValRat 3 x ≤ padicValRat 3 ((c : ℚ) * x ^ a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow _]
  have hcval := n35_val_int_nonneg c
  omega

private theorem n35TripleDen_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hcurve : OnE35Short x y)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (n35TripleDen x) = 1 - 8 * k := by
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hz
    apply n35TripleDen_ne_zero hx hcurve
    unfold n35TripleDen
    rw [hz]
    ring
  have hv3x : padicValRat 3 (3 * x) = 1 - 2 * k := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 :=
      padicValRat.self (p := 3) (by norm_num)
    rw [padicValRat.mul (by norm_num) hx, hthree, hvx]
    ring
  have hvlin : padicValRat 3 (3 * x + 28) = 1 - 2 * k := by
    rw [n35_val_add_eq_left_of_lt (a := 3 * x) (b := 28)
      (mul_ne_zero (by norm_num) hx) (by
        rw [hv3x]
        have h28 : 0 ≤ padicValRat 3 (28 : ℚ) := by
          simpa using n35_val_int_nonneg 28
        omega), hv3x]
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hvquad : padicValRat 3 (x ^ 2 + 12 * x + 336) = -4 * k := by
    have hshape : x ^ 2 + 12 * x + 336 =
        x ^ 2 + [12 * x, (336 : ℚ)].sum := by simp; ring
    rw [hshape, n35_val_add_list_eq (q := x ^ 2)]
    · rw [padicValRat.pow _, hvx]
      ring
    · exact pow_ne_zero 2 hx
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · have hge := n35_val_monomial_ge hx hy 12 (by norm_num) 1 0
        rw [padicValRat.pow _, hvx]
        norm_num at hge ⊢
        omega
      · have hge := n35_val_int_nonneg 336
        rw [padicValRat.pow _, hvx]
        norm_num at hge ⊢
        omega
  unfold n35TripleDen
  rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
    padicValRat.mul hx hlin, hvx, hvlin, hvquad]
  ring

private theorem n35TripleXNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (n35TripleXNum x) = -18 * k := by
  let l : List ℚ :=
    [-2688 * x ^ 7, -103936 * x ^ 6, -1204224 * x ^ 5,
      -4214784 * x ^ 4, 119418880 * x ^ 3, 1888223232 * x ^ 2,
      13217562624 * x, (30840979456 : ℚ)]
  have hshape : n35TripleXNum x = x ^ 9 + l.sum := by
    simp [n35TripleXNum, l]
    ring
  rw [hshape, n35_val_add_list_eq (q := x ^ 9)]
  · rw [padicValRat.pow _, hvx]
    ring
  · exact pow_ne_zero 9 hx
  · intro z hz
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow _, hvx]
    · have hge := n35_val_monomial_ge hx hy (-2688) (by norm_num) 7 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy (-103936) (by norm_num) 6 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy (-1204224) (by norm_num) 5 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy (-4214784) (by norm_num) 4 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy 119418880 (by norm_num) 3 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy 1888223232 (by norm_num) 2 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_monomial_ge hx hy 13217562624 (by norm_num) 1 0
      rw [hvx] at hge; norm_num at hge ⊢; omega
    · have hge := n35_val_int_nonneg 30840979456
      norm_num at hge ⊢; omega

private theorem n35_val_leading_poly {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k)
    (n : ℕ) (hn : 0 < n) (l : List (ℤ × ℕ))
    (hval : ∀ cb ∈ l, -2 * (n : ℤ) * k < -2 * (cb.2 : ℤ) * k)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    padicValRat 3 (x ^ n + (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) =
      -2 * (n : ℤ) * k := by
  rw [n35_val_add_list_eq (q := x ^ n)]
  · rw [padicValRat.pow _, hvx]
    ring
  · exact pow_ne_zero n hx
  · intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨cb, hcb, rfl⟩ := hz
    have hge := n35_val_monomial_ge hx hy cb.1 (hcoeff cb hcb) cb.2 0
    rw [hvx] at hge
    have hlead : padicValRat 3 (x ^ n) = -2 * (n : ℤ) * k := by
      rw [padicValRat.pow _, hvx]
      ring
    rw [hlead]
    norm_num at hge ⊢
    have hge' : -2 * (cb.2 : ℤ) * k ≤
        padicValRat 3 ((cb.1 : ℚ) * x ^ cb.2) := by
      convert hge using 1 <;> ring
    have hchain := (hval cb hcb).trans_le hge'
    rw [show -(2 * (n : ℤ) * k) = -2 * (n : ℤ) * k by ring]
    exact hchain

private theorem n35TripleYNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k)
    (hvy : padicValRat 3 y = -3 * k) :
    padicValRat 3 (n35TripleYNum x y) = -27 * k := by
  let l1 : List (ℤ × ℕ) := [(-448, 1), (-6272, 0)]
  let l2 : List (ℤ × ℕ) := [(28, 2), (-112, 1), (3136, 0)]
  let l3 : List (ℤ × ℕ) :=
    [(36, 5), (4480, 4), (82880, 3), (878080, 2),
      (4566016, 1), (9834496, 0)]
  have hv1 : padicValRat 3 (x ^ 3 - 448 * x - 6272) = -6 * k := by
    have h := n35_val_leading_poly hx hy hk hvx 3 (by norm_num) l1
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num <;> omega)
      (by intro cb hcb; simp [l1] at hcb; rcases hcb with rfl | rfl <;> norm_num)
    convert h using 1 <;> simp [l1] <;> ring
  have hv2 : padicValRat 3 (x ^ 3 + 28 * x ^ 2 - 112 * x + 3136) =
      -6 * k := by
    have h := n35_val_leading_poly hx hy hk hvx 3 (by norm_num) l2
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num)
    convert h using 1 <;> simp [l2] <;> ring
  have hv3 : padicValRat 3
      (x ^ 6 + 36 * x ^ 5 + 4480 * x ^ 4 + 82880 * x ^ 3 +
        878080 * x ^ 2 + 4566016 * x + 9834496) = -12 * k := by
    have h := n35_val_leading_poly hx hy hk hvx 6 (by norm_num) l3
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    convert h using 1 <;> simp [l3] <;> ring
  have hf1 : x ^ 3 - 448 * x - 6272 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv1
    omega
  have hf2 : x ^ 3 + 28 * x ^ 2 - 112 * x + 3136 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv2
    omega
  have hf3 : x ^ 6 + 36 * x ^ 5 + 4480 * x ^ 4 + 82880 * x ^ 3 +
      878080 * x ^ 2 + 4566016 * x + 9834496 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv3
    omega
  unfold n35TripleYNum
  rw [padicValRat.mul
      (mul_ne_zero (mul_ne_zero hy hf1) hf2) hf3,
    padicValRat.mul (mul_ne_zero hy hf1) hf2,
    padicValRat.mul hy hf1, hvy, hv1, hv2, hv3]
  ring

def E35FormalAtThree : E35ShortPoint → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k

def E35FormalLevel : E35ShortPoint → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k

theorem E35FormalAtThree_iff (P : E35ShortPoint) :
    E35FormalAtThree P ↔ P = 0 ∨ ∃ k : ℤ, E35FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [E35FormalAtThree, E35FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

private theorem n35_threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : threeIsogenyX x ≠ 0 := by
  rw [threeIsogenyX_eq_den x hx]
  exact div_ne_zero
    (mul_ne_zero (by norm_num) (n35TripleDen_ne_zero hx h))
    (pow_ne_zero 3 hx)

theorem E35FormalLevel_triple {P : E35ShortPoint} {k : ℤ}
    (hP : E35FormalLevel P k) :
    E35FormalLevel (3 • P) (k + 1) := by
  cases P with
  | zero => simp [E35FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      have hdval := n35TripleDen_val hx hy hk hcurve hvx
      have hXval := n35TripleXNum_val hx hy hk hvx
      have hYval := n35TripleYNum_val hx hy hk hvx hvy
      have hd : n35TripleDen x ≠ 0 := n35TripleDen_ne_zero hx hcurve
      have hX : n35TripleXNum x ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hXval
        omega
      have hY : n35TripleYNum x y ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hYval
        omega
      have hphi := n35_threeIsogenyX_ne_zero hx hcurve
      have hcomp := dual_comp_threeIsogenyPoint
        (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint)
      rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
      unfold WeierstrassCurve.Affine.Point.mk at hcomp
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
      rw [← hcomp]
      change 0 < k + 1 ∧
        padicValRat 3 (dualThreeIsogenyX (threeIsogenyX x)) = -2 * (k + 1) ∧
        padicValRat 3
          (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) =
            -3 * (k + 1)
      refine ⟨by omega, ?_, ?_⟩
      · rw [n35TripleX_formula hx hcurve,
          padicValRat.div hX (pow_ne_zero 2 hd), hXval,
          padicValRat.pow _, hdval]
        ring
      · rw [n35TripleY_formula hx hcurve,
          padicValRat.div hY (pow_ne_zero 3 hd), hYval,
          padicValRat.pow _, hdval]
        ring

/-- Tripling preserves the formal kernel at three. -/
theorem E35FormalAtThree_triple {P : E35ShortPoint}
    (hP : E35FormalAtThree P) : E35FormalAtThree (3 • P) := by
  rw [E35FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k + 1, E35FormalLevel_triple hk⟩

/-- At the good prime three, an affine rational point is integral or belongs
to the formal kernel. -/
theorem E35_formal_or_integral (P : E35ShortPoint) :
    E35FormalAtThree P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 3 x ∧ 0 ≤ padicValRat 3 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
      let vx := padicValRat 3 x
      let vy := padicValRat 3 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [-(x ^ 3), -(16 * x ^ 2), -(224 * x), (-784 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnE35Short at hE
          linear_combination hE
        have hlead : padicValRat 3 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow _]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 3 (y ^ 2) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow x, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := n35_val_x_monomial_ge hx0 16 (by norm_num) 2
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              norm_num at hge
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := n35_val_x_monomial_ge hx0 224 (by norm_num) 1
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              norm_num at hge
              omega
          · have hge := n35_val_int_nonneg (-784)
            rw [hlead]
            norm_num at hge ⊢
            omega
        have hval := n35_val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, -(16 * x ^ 2), -(224 * x), (-784 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnE35Short at hE
            linear_combination hE
          have hlead : padicValRat 3 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow _]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 3 (-(x ^ 3)) < padicValRat 3 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · simp [hy0, hlead]
                omega
              · rw [padicValRat.pow y, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · have hge := n35_val_x_monomial_ge hx 16 (by norm_num) 2
              simp only [padicValRat.neg]
              rw [padicValRat.pow _]
              dsimp [vx] at hvxneg hge ⊢
              norm_num at hge
              omega
            · have hge := n35_val_x_monomial_ge hx 224 (by norm_num) 1
              simp only [padicValRat.neg]
              rw [padicValRat.pow _]
              dsimp [vx] at hvxneg hge ⊢
              norm_num at hge
              omega
            · have hge := n35_val_int_nonneg (-784)
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval := n35_val_add_list_eq l
            (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let l : List ℚ := [16 * x ^ 2, 224 * x, (784 : ℚ)]
        have hshape : x ^ 3 + l.sum =
            x ^ 3 + 16 * x ^ 2 + 224 * x + 784 := by
          simp [l]
          ring
        have hgt : ∀ a ∈ l,
            padicValRat 3 (x ^ 3) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · have hge := n35_val_x_monomial_ge hx 16 (by norm_num) 2
            rw [padicValRat.pow _]
            dsimp [vx] at hvxneg hge ⊢
            norm_num at hge
            omega
          · have hge := n35_val_x_monomial_ge hx 224 (by norm_num) 1
            rw [padicValRat.pow _]
            dsimp [vx] at hvxneg hge ⊢
            norm_num at hge
            omega
          · have hge := n35_val_int_nonneg 784
            rw [padicValRat.pow _]
            dsimp [vx] at hvxneg ⊢
            norm_num at hge ⊢
            omega
        have hvright := n35_val_add_list_eq l (pow_ne_zero 3 hx) hgt
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 3 (y ^ 2) := by
              rw [padicValRat.pow _]
              dsimp [vy]
            _ = padicValRat 3 (x ^ 3 + (4 * x + 28) ^ 2) := by rw [hE]
            _ = padicValRat 3 (x ^ 3 + 16 * x ^ 2 + 224 * x + 784) := by
              congr 1
              ring
            _ = padicValRat 3 (x ^ 3 + l.sum) := by rw [hshape]
            _ = 3 * vx := by
              rw [hvright, padicValRat.pow _]
              dsimp [vx]
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

private noncomputable def n35RatPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 3 q) : ℤ_[3] :=
  ⟨(q : ℚ_[3]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

private theorem n35RatPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 3 q) :
    PadicInt.toZMod (n35RatPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[3])‖ < 1
  have hqcast : (q : ℚ_[3]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (3 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (3 : ℝ))
    (by norm_num : (1 : ℝ) < 3)).2 (by omega)

private theorem n35_val_pos_of_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (n35RatPadicInt q hqi) = 0) :
    0 < padicValRat 3 q := by
  by_contra hnot
  have hv0 : padicValRat 3 q = 0 := by omega
  have hm : n35RatPadicInt q hqi ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [← PadicInt.ker_toZMod]
    exact hred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖(q : ℚ_[3])‖ < 1 at hm
  have hqcast : (q : ℚ_[3]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv0] at hm
  norm_num at hm

private theorem n35_val_zero_of_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (n35RatPadicInt q hqi) ≠ 0) :
    padicValRat 3 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 3 q := lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := n35RatPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : n35RatPadicInt q hqi =
      n35RatPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

private theorem n35_padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnE35Short x y) :
    (n35RatPadicInt y hy) ^ 2 =
      (n35RatPadicInt x hx) ^ 3 + 16 * (n35RatPadicInt x hx) ^ 2 +
        224 * n35RatPadicInt x hx + 784 := by
  apply Subtype.ext
  change (y : ℚ_[3]) ^ 2 =
    (x : ℚ_[3]) ^ 3 + 16 * (x : ℚ_[3]) ^ 2 + 224 * (x : ℚ_[3]) + 784
  unfold OnE35Short at hE
  push_cast
  exact_mod_cast (show y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784 by
    nlinarith [hE])

set_option maxHeartbeats 0 in
private theorem n35_mod_three_affine_points :
    ∀ X Y : ZMod 3,
      Y ^ 2 = X ^ 3 + 16 * X ^ 2 + 224 * X + 784 → X = 0 ∧ Y ≠ 0 := by
  decide

private theorem n35_integral_reduction {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnE35Short x y) :
    PadicInt.toZMod (n35RatPadicInt x hx) = 0 ∧
      PadicInt.toZMod (n35RatPadicInt y hy) ≠ 0 := by
  have hpadic := n35_padicInt_equation hx hy hE
  have hred :
      PadicInt.toZMod (n35RatPadicInt y hy) ^ 2 =
        PadicInt.toZMod (n35RatPadicInt x hx) ^ 3 +
          16 * PadicInt.toZMod (n35RatPadicInt x hx) ^ 2 +
          224 * PadicInt.toZMod (n35RatPadicInt x hx) + 784 := by
    simpa only [map_pow, map_add, map_mul, map_ofNat] using
      congrArg PadicInt.toZMod hpadic
  exact n35_mod_three_affine_points _ _ hred

private theorem n35_val_int_unit (z : ℤ) (hz : ¬(3 : ℤ) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  norm_num

private theorem n35_val_unit_constant_poly
    {x : ℚ} (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x)
    (c : ℤ) (hc : ¬(3 : ℤ) ∣ c) (l : List (ℤ × ℕ))
    (hexp : ∀ cb ∈ l, 0 < cb.2)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    (c : ℚ) + (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 ∧
      padicValRat 3
        ((c : ℚ) + (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) = 0 := by
  have hc0 : (c : ℚ) ≠ 0 := by
    exact Int.cast_ne_zero.mpr (fun hz => hc (by simp [hz]))
  have hgt : ∀ a ∈ (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2),
      padicValRat 3 (c : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨cb, hcb, rfl⟩ := ha
    have hge := n35_val_x_monomial_ge hx cb.1 (hcoeff cb hcb) cb.2
    rw [n35_val_int_unit c hc]
    have hp := hexp cb hcb
    have hpZ : (0 : ℤ) < (cb.2 : ℤ) := by exact_mod_cast hp
    exact (mul_pos hpZ hvx).trans_le hge
  have hval := n35_val_add_list_eq
    (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hc0 hgt
  have hne : (c : ℚ) +
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 := by
    intro hz
    have hsum :
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum = -(c : ℚ) := by
      linarith
    rcases n35_val_sum_gt_or_zero
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hgt with hzero | hsumgt
    · rw [hzero] at hsum
      exact hc0 (by linarith)
    · rw [hsum, padicValRat.neg] at hsumgt
      omega
  exact ⟨hne, by rw [hval, n35_val_int_unit c hc]⟩

private theorem n35TripleDen_val_integral {x y : ℚ}
    (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x)
    (hcurve : OnE35Short x y) :
    padicValRat 3 (n35TripleDen x) = padicValRat 3 x + 1 := by
  have hd := n35TripleDen_ne_zero hx hcurve
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hz
    apply hd
    unfold n35TripleDen
    rw [hz]
    ring
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hv3 : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (p := 3) (by norm_num)
  have hv28 : padicValRat 3 (28 : ℚ) = 0 :=
    n35_val_int_unit 28 (by norm_num)
  have hv3x : padicValRat 3 (3 * x) = 1 + padicValRat 3 x := by
    rw [padicValRat.mul (by norm_num) hx, hv3]
  have hvlin : padicValRat 3 (3 * x + 28) = 0 := by
    rw [add_comm, n35_val_add_eq_left_of_lt (a := (28 : ℚ))
      (b := 3 * x) (by norm_num) (by rw [hv28, hv3x]; omega), hv28]
  have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
    n35_val_int_unit 4 (by norm_num)
  have hv12 : padicValRat 3 (12 : ℚ) = 1 := by
    rw [show (12 : ℚ) = 3 * 4 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv4]
    norm_num
  have hv112 : padicValRat 3 (112 : ℚ) = 0 :=
    n35_val_int_unit 112 (by norm_num)
  have hv336 : padicValRat 3 (336 : ℚ) = 1 := by
    rw [show (336 : ℚ) = 3 * 112 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv112]
    norm_num
  let l : List ℚ := [x ^ 2, 12 * x]
  have hshape : (336 : ℚ) + l.sum = x ^ 2 + 12 * x + 336 := by
    simp [l]
    ring
  have hgt : ∀ a ∈ l,
      padicValRat 3 (336 : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hv336, padicValRat.pow _]
      omega
    · rw [hv336, padicValRat.mul (by norm_num) hx, hv12]
      omega
  have hvquad := n35_val_add_list_eq l (by norm_num) hgt
  rw [hshape, hv336] at hvquad
  unfold n35TripleDen
  rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
    padicValRat.mul hx hlin, hvlin, hvquad]
  ring

private theorem n35TripleXNum_val_integral {x : ℚ}
    (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x) :
    n35TripleXNum x ≠ 0 ∧ padicValRat 3 (n35TripleXNum x) = 0 := by
  let l : List (ℤ × ℕ) :=
    [(1, 9), (-2688, 7), (-103936, 6), (-1204224, 5),
      (-4214784, 4), (119418880, 3), (1888223232, 2),
      (13217562624, 1)]
  have h := n35_val_unit_constant_poly hx hvx 30840979456 (by norm_num) l
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hshape : ((30840979456 : ℤ) : ℚ) +
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum = n35TripleXNum x := by
    simp [l, n35TripleXNum]
    ring
  rw [hshape] at h
  exact h

private theorem n35TripleYNum_val_integral {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvx : 0 < padicValRat 3 x) (hvy : padicValRat 3 y = 0) :
    n35TripleYNum x y ≠ 0 ∧ padicValRat 3 (n35TripleYNum x y) = 0 := by
  let l1 : List (ℤ × ℕ) := [(1, 3), (-448, 1)]
  let l2 : List (ℤ × ℕ) := [(1, 3), (28, 2), (-112, 1)]
  let l3 : List (ℤ × ℕ) :=
    [(1, 6), (36, 5), (4480, 4), (82880, 3), (878080, 2),
      (4566016, 1)]
  have h1 := n35_val_unit_constant_poly hx hvx (-6272) (by norm_num) l1
    (by intro cb hcb; simp [l1] at hcb; rcases hcb with rfl | rfl <;> norm_num)
    (by intro cb hcb; simp [l1] at hcb; rcases hcb with rfl | rfl <;> norm_num)
  have h2 := n35_val_unit_constant_poly hx hvx 3136 (by norm_num) l2
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
  have h3 := n35_val_unit_constant_poly hx hvx 9834496 (by norm_num) l3
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  have hs1 : (((-6272 : ℤ) : ℚ)) +
      (l1.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 - 448 * x - 6272 := by simp [l1]; ring
  have hs2 : ((3136 : ℤ) : ℚ) +
      (l2.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 + 28 * x ^ 2 - 112 * x + 3136 := by simp [l2]; ring
  have hs3 : ((9834496 : ℤ) : ℚ) +
      (l3.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 6 + 36 * x ^ 5 + 4480 * x ^ 4 + 82880 * x ^ 3 +
          878080 * x ^ 2 + 4566016 * x + 9834496 := by
    simp [l3]
    ring
  rw [hs1] at h1
  rw [hs2] at h2
  rw [hs3] at h3
  rcases h1 with ⟨hne1, hv1⟩
  rcases h2 with ⟨hne2, hv2⟩
  rcases h3 with ⟨hne3, hv3⟩
  constructor
  · unfold n35TripleYNum
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3
  · unfold n35TripleYNum
    rw [padicValRat.mul (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3,
      padicValRat.mul (mul_ne_zero hy hne1) hne2,
      padicValRat.mul hy hne1, hvy, hv1, hv2, hv3]
    ring

/-- Three times every rational point belongs to the formal kernel at three. -/
theorem E35_three_nsmul_formal (P : E35ShortPoint) :
    E35FormalAtThree (3 • P) := by
  rcases E35_formal_or_integral P with hformal | hintegral
  · exact E35FormalAtThree_triple hformal
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hxint, hyint⟩
        have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
        by_cases hx0 : x = 0
        · have hphi : threeIsogenyPoint
              (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) =
                (0 : E35DualPoint) := by
            simp only [threeIsogenyPoint]
            rw [dif_pos hx0]
            rfl
          have hcomp := dual_comp_threeIsogenyPoint
            (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint)
          rw [hphi, dualThreeIsogenyPoint_zero] at hcomp
          rw [← hcomp]
          trivial
        · obtain ⟨hxred, hyred⟩ := n35_integral_reduction hxint hyint hcurve
          have hvxpos := n35_val_pos_of_padicInt_red_zero hx0 hxint hxred
          have hy0 : y ≠ 0 := by
            intro hyzero
            apply hyred
            subst y
            simp [n35RatPadicInt]
          have hvy0 := n35_val_zero_of_padicInt_red_nonzero hy0 hyint hyred
          have hdval := n35TripleDen_val_integral hx0 hvxpos hcurve
          obtain ⟨hX, hXval⟩ := n35TripleXNum_val_integral hx0 hvxpos
          obtain ⟨hY, hYval⟩ :=
            n35TripleYNum_val_integral hx0 hy0 hvxpos hvy0
          have hd : n35TripleDen x ≠ 0 := n35TripleDen_ne_zero hx0 hcurve
          have hphi := n35_threeIsogenyX_ne_zero hx0 hcurve
          have hcomp := dual_comp_threeIsogenyPoint
            (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint)
          rw [threeIsogenyPoint_some_of_x_ne_zero h hx0] at hcomp
          unfold WeierstrassCurve.Affine.Point.mk at hcomp
          rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
          rw [← hcomp]
          change ∃ k : ℤ, 0 < k ∧
            padicValRat 3 (dualThreeIsogenyX (threeIsogenyX x)) = -2 * k ∧
            padicValRat 3
              (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) =
                -3 * k
          refine ⟨padicValRat 3 x + 1, by omega, ?_, ?_⟩
          · rw [n35TripleX_formula hx0 hcurve,
              padicValRat.div hX (pow_ne_zero 2 hd), hXval,
              padicValRat.pow _, hdval]
            ring
          · rw [n35TripleY_formula hx0 hcurve,
              padicValRat.div hY (pow_ne_zero 3 hd), hYval,
              padicValRat.pow _, hdval]
            ring

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 1142-1205
private theorem E35FormalLevel_unique {P : E35ShortPoint} {k l : ℤ}
    (hk : E35FormalLevel P k) (hl : E35FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [E35FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

theorem E35FormalLevel_three_power {P : E35ShortPoint} {k : ℤ}
    (hP : E35FormalLevel P k) (n : ℕ) :
    ∃ k' : ℤ, k' = k + (n : ℤ) ∧
      E35FormalLevel ((3 ^ n : ℕ) • P) k' := by
  induction n with
  | zero => exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      obtain ⟨l, hl, hlevel⟩ := ih
      have hpow : (3 ^ (n + 1) : ℕ) • P =
          3 • ((3 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      refine ⟨l + 1, by norm_num at hl ⊢; omega, ?_⟩
      rw [hpow]
      exact E35FormalLevel_triple hlevel

theorem E35_formal_separated (P : E35ShortPoint)
    (hP : E35FormalAtThree P)
    (hdiv : ∀ n : ℕ, ∃ Q : E35ShortPoint,
      E35FormalAtThree Q ∧ P = (3 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, E35FormalLevel P k := by
    rw [E35FormalAtThree_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, E35FormalLevel Q l := by
    rw [E35FormalAtThree_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  obtain ⟨l', hl', hlevel⟩ := E35FormalLevel_three_power hl n
  have hlevelP' : E35FormalLevel P l' := by
    rw [hPQ]
    exact hlevel
  have heq : l' = k := E35FormalLevel_unique hlevelP' hk
  have hkNat : (k.toNat : ℤ) = k :=
    Int.toNat_of_nonneg (le_of_lt hkpos)
  have hncast : (n : ℤ) = k + 1 := by
    dsimp [n]
    push_cast
    rw [hkNat]
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [E35FormalLevel] at hl
    | some x y h => exact hl.1
  omega


end

end MazurProof.RationalPointsX135

end

open MazurHuang.ThreeIsogeny35

theorem solution
    (P : E35ShortPoint)
    (h : ∀ n : ℕ, ∃ Q : E35ShortPoint, 3 • P = (3 ^ n : ℕ) • (3 • Q)) :
    3 • P = 0 := by
  apply MazurProof.RationalPointsX135.E35_formal_separated (3 • P)
    (MazurProof.RationalPointsX135.E35_three_nsmul_formal P)
  intro n
  obtain ⟨Q, hQ⟩ := h n
  exact ⟨3 • Q, MazurProof.RationalPointsX135.E35_three_nsmul_formal Q, hQ⟩
