-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_three_nsmul_eq_three_pow_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:20:52.08857+00:00
-- url     : https://prove2.me/submissions/419a238d-fa34-4493-a592-656487d0942a

/-
Weak 3-descent on y^2 = x^3 + (4x+28)^2: 3P is divisible by every power of 3.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (exists_dualThreeIsogeny_preimage_of_alpha_cube)
  * FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean (the 3-torsion points (0, 28) and (0, -28), n35_threeIsogenyPoint_surjective,
    E35_weak_three_descent, E35_three_nsmul_three_power_divisible; the cube classes of the descent
    function, the surjectivity on affine points and the composition of the two isogenies are
    taken from published theorems)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35
import Theorems.Thm_MazurHuang_threeIsogeny35_alpha_eq_cube_class
import Theorems.Thm_MazurHuang_threeIsogeny35_exists_preimage_of_dual_equation
import Theorems.Thm_MazurHuang_threeIsogeny35_dual_comp_eq_three_nsmul

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean and FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

open MazurHuang.ThreeIsogeny35

/-- The explicit dual isogeny composed with the explicit three-isogeny is multiplication by three
(statement as in `FLT/Assumptions/MazurProof/RationalPointsX135.lean`), here the published theorem
`MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul`. -/
theorem dual_comp_threeIsogenyPoint (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P :=
  MazurHuang.threeIsogeny35_dual_comp_eq_three_nsmul P

/-- The cube classes of the first descent function (statement as in
`FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean`), here the published theorem
`MazurHuang.threeIsogeny35_alpha_eq_cube_class`. -/
theorem short_alpha_cubeclass {x y : ℚ}
    (h : y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784) :
    ∃ r : ℚ,
      y - (4 * x + 28) = r ^ 3 ∨
      y - (4 * x + 28) = 7 * r ^ 3 ∨
      y - (4 * x + 28) = 49 * r ^ 3 :=
  MazurHuang.threeIsogeny35_alpha_eq_cube_class h

/-- Every affine rational point of the dual curve is the image of an affine rational point under
the three-isogeny (statement as in `FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean`),
here the published theorem `MazurHuang.threeIsogeny35_exists_preimage_of_dual_equation`. -/
theorem n35_dual_affine_has_three_isogeny_preimage {s t : ℚ}
    (hdual : t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2) :
    ∃ x y : ℚ, x ≠ 0 ∧
      y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 ∧
      (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2 = s ∧
      (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3 = t :=
  MazurHuang.threeIsogeny35_exists_preimage_of_dual_equation hdual

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 1120-1180
/-- A cube value of the first three-descent function constructs an explicit
preimage under the dual three-isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hr : r ^ 3 = y - (4 * x + 28)) (hr0 : r ≠ 0) :
    ∃ Q : E35DualPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 4 * x + 28 := by linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 8 * x + 56) := by
    unfold OnE35Short at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 8 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 8 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 3000 * r / d
  let t : ℚ := 9 * s * r + 12 * s + 4500
  have hs : s ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hdual : OnE35Dual s t := by
    unfold OnE35Dual
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 729000000 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -729000000 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      19683000000000 * (-2 * r ^ 2 - 4 * r + x) * hrel
  have hdualns : WeierstrassCurve.Affine.Nonsingular E35DualCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E35DualCurve_equation_iff s t).mpr hdual)
  let Q : E35DualPoint := WeierstrassCurve.Affine.Point.some s t hdualns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 885-1140
private theorem E35T_nonsingular :
    WeierstrassCurve.Affine.Nonsingular E35ShortCurve (0 : ℚ) 28 :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((E35ShortCurve_equation_iff 0 28).mpr (by norm_num [OnE35Short]))

private theorem E35TNeg_nonsingular :
    WeierstrassCurve.Affine.Nonsingular E35ShortCurve (0 : ℚ) (-28) :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    ((E35ShortCurve_equation_iff 0 (-28)).mpr (by norm_num [OnE35Short]))

def E35T : E35ShortPoint :=
  WeierstrassCurve.Affine.Point.some 0 28 E35T_nonsingular

def E35TNeg : E35ShortPoint :=
  WeierstrassCurve.Affine.Point.some 0 (-28) E35TNeg_nonsingular

@[simp] theorem E35TNeg_eq_neg : E35TNeg = -E35T := by
  rw [E35TNeg, E35T, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rfl
  · simp [WeierstrassCurve.Affine.negY, E35ShortCurve]

private theorem n35_three_nsmul_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hx : x = 0) :
    3 • (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) = 0 := by
  have hphi : threeIsogenyPoint
      (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) =
        (0 : E35DualPoint) := by
    simp only [threeIsogenyPoint]
    rw [dif_pos hx]
    rfl
  have hcomp := dual_comp_threeIsogenyPoint
    (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint)
  rw [hphi, dualThreeIsogenyPoint_zero] at hcomp
  exact hcomp.symm

@[simp] theorem E35T_three_nsmul : 3 • E35T = 0 := by
  exact n35_three_nsmul_of_x_zero E35T_nonsingular rfl

@[simp] theorem E35TNeg_three_nsmul : 3 • E35TNeg = 0 := by
  exact n35_three_nsmul_of_x_zero E35TNeg_nonsingular rfl

private theorem n35_add_T_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnE35Short x y) :
    let L := WeierstrassCurve.Affine.slope E35ShortCurve x 0 y 28
    let X := WeierstrassCurve.Affine.addX E35ShortCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY E35ShortCurve x 0 y L
    Y - (4 * X + 28) = -3136 * (y - (4 * x + 28)) / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX E35ShortCurve
  field_simp [hx]
  unfold OnE35Short at hcurve
  linear_combination -(x ^ 3) * (4 * x + y - 84) * hcurve

private theorem n35_add_TNeg_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnE35Short x y) :
    let L := WeierstrassCurve.Affine.slope E35ShortCurve x 0 y (-28)
    let X := WeierstrassCurve.Affine.addX E35ShortCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY E35ShortCurve x 0 y L
    Y - (4 * X + 28) =
      -56 * (y + (4 * x + 28)) ^ 2 / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX E35ShortCurve
  field_simp [hx]
  unfold OnE35Short at hcurve
  linear_combination -(x ^ 3) * (4 * x + y + 28) * hcurve

/-- The explicit arithmetic descent on the dual curve makes the first
three-isogeny surjective on rational points. -/
theorem n35_threeIsogenyPoint_surjective (Q : E35DualPoint) :
    ∃ P : E35ShortPoint, threeIsogenyPoint P = Q := by
  cases Q with
  | zero => exact ⟨0, threeIsogenyPoint_zero⟩
  | some s t h =>
      have hdual : OnE35Dual s t := (E35DualCurve_equation_iff s t).mp h.1
      obtain ⟨x, y, hx, hcurve, hX, hY⟩ :=
        n35_dual_affine_has_three_isogeny_preimage hdual
      have hns : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y :=
        WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          ((E35ShortCurve_equation_iff x y).mpr hcurve)
      refine ⟨WeierstrassCurve.Affine.Point.some x y hns, ?_⟩
      rw [threeIsogenyPoint_some_of_x_ne_zero hns hx]
      change WeierstrassCurve.Affine.Point.some
          (threeIsogenyX x) (threeIsogenyY x y) _ =
        WeierstrassCurve.Affine.Point.some s t h
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩

/-- First three-descent: every rational point is a threefold multiple up to
one of the two nonzero rational three-torsion points. -/
theorem E35_weak_three_descent (P : E35ShortPoint) :
    ∃ Q : E35ShortPoint,
      P = 3 • Q ∨ P = E35T + 3 • Q ∨ P = E35TNeg + 3 • Q := by
  cases P with
  | zero => exact ⟨0, Or.inl (by rfl)⟩
  | some x y h =>
      have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (28 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnE35Short] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 28 hySq with hy | hy
        · refine ⟨0, Or.inr (Or.inl ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h = E35T + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [E35T, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
        · refine ⟨0, Or.inr (Or.inr ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h = E35TNeg + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [E35TNeg, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
      · have hcubic :
            y ^ 2 = x ^ 3 + 16 * x ^ 2 + 224 * x + 784 := by
          calc
            y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2 := hcurve
            _ = x ^ 3 + 16 * x ^ 2 + 224 * x + 784 := by ring
        have hab :
            (y - (4 * x + 28)) * (y + (4 * x + 28)) = x ^ 3 := by
          calc
            (y - (4 * x + 28)) * (y + (4 * x + 28)) =
                y ^ 2 - (4 * x + 28) ^ 2 := by ring
            _ = x ^ 3 := by rw [hcurve]; ring
        obtain ⟨r, halpha | halpha | halpha⟩ := short_alpha_cubeclass hcubic
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by rw [← hab, halpha]; ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube h halpha.symm hr
          obtain ⟨Q, hQ⟩ := n35_threeIsogenyPoint_surjective Qd
          refine ⟨Q, Or.inl ?_⟩
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                dualThreeIsogenyPoint Qd := hQd.symm
            _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by rw [hQ]
            _ = 3 • Q := dual_comp_threeIsogenyPoint Q
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by rw [← hab, halpha]; ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L := WeierstrassCurve.Affine.slope E35ShortCurve x 0 y 28
          let X := WeierstrassCurve.Affine.addX E35ShortCurve x 0 L
          let Y := WeierstrassCurve.Affine.addY E35ShortCurve x 0 y L
          let hns : WeierstrassCurve.Affine.Nonsingular E35ShortCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h E35T_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : E35ShortPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) + E35T =
                Pplus := by
            rw [E35T]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -28 * r / x
          have hrp : rp ≠ 0 := by
            exact div_ne_zero (mul_ne_zero (by norm_num) hr) hx
          have halphaP : rp ^ 3 = Y - (4 * X + 28) := by
            symm
            have hid := n35_add_T_alpha_identity hx hcurve
            change Y - (4 * X + 28) =
              -3136 * (y - (4 * x + 28)) / x ^ 3 at hid
            rw [hid, halpha]
            dsimp [rp]
            field_simp [hx]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube hns halphaP hrp
          obtain ⟨Q, hQ⟩ := n35_threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) + E35T =
                3 • Q := hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inr ?_)⟩
          rw [E35TNeg_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                -E35T +
                  ((WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) +
                    E35T) := by abel
            _ = -E35T + 3 • Q := by rw [hsum]
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by rw [← hab, halpha]; ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L := WeierstrassCurve.Affine.slope E35ShortCurve x 0 y (-28)
          let X := WeierstrassCurve.Affine.addX E35ShortCurve x 0 L
          let Y := WeierstrassCurve.Affine.addY E35ShortCurve x 0 y L
          let hns : WeierstrassCurve.Affine.Nonsingular E35ShortCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h E35TNeg_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : E35ShortPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) + E35TNeg =
                Pplus := by
            rw [E35TNeg]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -2 * x / (7 * r ^ 2)
          have hrp : rp ≠ 0 := by
            exact div_ne_zero (mul_ne_zero (by norm_num) hx)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
          have halphaP : rp ^ 3 = Y - (4 * X + 28) := by
            symm
            have hid := n35_add_TNeg_alpha_identity hx hcurve
            change Y - (4 * X + 28) =
              -56 * (y + (4 * x + 28)) ^ 2 / x ^ 3 at hid
            rw [hid]
            have hbeta : y + (4 * x + 28) = x ^ 3 / (49 * r ^ 3) := by
              apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))).2
              rw [← hab, halpha]
              ring
            rw [hbeta]
            dsimp [rp]
            field_simp [hx, hr]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube hns halphaP hrp
          obtain ⟨Q, hQ⟩ := n35_threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) + E35TNeg =
                3 • Q := hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inl ?_)⟩
          rw [E35TNeg_eq_neg] at hsum
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                E35T +
                  ((WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) -
                    E35T) := by abel
            _ = E35T + 3 • Q := by
              congr 1

-- FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean, lines 1207-1227
theorem E35_three_nsmul_three_power_divisible
    (P : E35ShortPoint) (n : ℕ) :
    ∃ Q : E35ShortPoint,
      3 • P = (3 ^ n : ℕ) • (3 • Q) := by
  induction n with
  | zero => exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨R, hR | hR | hR⟩ := E35_weak_three_descent Q
      all_goals
        have hthreeQ : 3 • Q = 3 • (3 • R) := by
          subst Q
          simp [nsmul_add]
        refine ⟨R, ?_⟩
        calc
          3 • P = (3 ^ n : ℕ) • (3 • Q) := hQ
          _ = (3 ^ n : ℕ) • (3 • (3 • R)) := by rw [hthreeQ]
          _ = (3 ^ (n + 1) : ℕ) • (3 • R) := by
            have hp : (3 ^ (n + 1) : ℕ) = 3 ^ n * 3 := by
              simp [pow_succ, Nat.mul_comm]
            rw [hp, mul_nsmul']


end

end MazurProof.RationalPointsX135

end

open MazurHuang.ThreeIsogeny35

theorem solution
    (P : E35ShortPoint) (n : ℕ) :
    ∃ Q : E35ShortPoint, 3 • P = (3 ^ n : ℕ) • (3 • Q) :=
  MazurProof.RationalPointsX135.E35_three_nsmul_three_power_divisible P n
