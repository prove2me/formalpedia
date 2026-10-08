-- Prove2me | solution 1 for MazurHuang.threeIsogeny35_dual_comp_Y_eq_tripleY
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:12:37.527851+00:00
-- url     : https://prove2.me/submissions/a7d6e7cc-d619-4324-baab-b4a2a9464242

/-
The dual 3-isogeny after the 3-isogeny: the y-coordinate is that of 3P.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (nonvanishing lemmas, shortDoubleX_sub_identity, shortDoubleX_ne_self, dual_three_comp_y;
    curves, isogeny formulas and tripling formulas come from the platform definition)
  * the published statement
-/
import Mathlib
import Definitions.Def_MazurHuang_ThreeIsogeny35

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

open MazurHuang.ThreeIsogeny35

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 792-831
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

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 846-870
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

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 983-1003
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

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 1032-1066
private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      shortTripleY x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyY shortTripleY shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX threeIsogenyY shortDoubleY shortDoubleX shortTangent
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
  have hy12 : y ^ 12 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 6 := by
    calc
      y ^ 12 = (y ^ 2) ^ 6 := by ring
      _ = _ := by rw [h]
  have hy10 : y ^ 10 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 5 := by
    calc
      y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [hy4, hy6, hy8, hy10, hy12]
  ring


end

end MazurProof.RationalPointsX135

end

open MazurHuang.ThreeIsogeny35

theorem solution
    {x y : ℚ} (hx : x ≠ 0) (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) = shortTripleY x y :=
  MazurProof.RationalPointsX135.dual_three_comp_y hx h
