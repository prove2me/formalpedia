-- Prove2me | solution 1 for OAI.PiExponent.window_from_small_parameter
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-15T05:30:28.275796+00:00
-- url     : https://prove2.me/submissions/79ce15ad-a0f9-4bc1-9843-a427c9066706

-- Adapted from Eyal1990 submission d4337bfd-5120-46f3-9a19-92163596dbcc.
-- Corrects cancellation by a positive real multiplier for this Mathlib pin.
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (nu : ℝ) (hnu : 2 < nu)
    (q : ℚ) (hqpos : 0 < (q : ℝ))
    (hqsmall : (q : ℝ) < min (1 / 4 : ℝ) (3 * (nu - 2) / (4 * (nu - 1)))) :
    ∃ (theta : ℚ) (A eta : ℝ),
      theta = (1 - q) ^ 2 ∧
      A = 1 - (q : ℝ) - ((nu - 2) / (8 * nu)) * (q : ℝ) ∧
      eta = ((nu - 2) / (8 * nu)) * (q : ℝ) ∧
      0 < theta ∧ theta < 1 ∧
      0 < A ∧ A < 1 ∧ 0 < eta ∧ eta < 1 ∧
      A ^ 2 < (theta : ℝ) ∧
      0 < nu * (A * (1 - eta) - (theta : ℝ)) -
        (1 - (theta : ℝ)) := by
  let x : Real := (q : Real)
  let c : Real := (nu - 2) / (8 * nu)
  let theta : Rat := (1 - q) ^ 2
  let A : Real := 1 - x - c * x
  let eta : Real := c * x
  have hnu0 : 0 < nu := by linarith only [hnu]
  have hden : 0 < 8 * nu := mul_pos (by norm_num) hnu0
  have hrel : c * (8 * nu) = nu - 2 := by
    dsimp only [c]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  have hxpos : 0 < x := hqpos
  have hxquarter : x < 1 / 4 :=
    lt_of_lt_of_le hqsmall (min_le_left _ _)
  have hxdet : x < 3 * (nu - 2) / (4 * (nu - 1)) :=
    lt_of_lt_of_le hqsmall (min_le_right _ _)
  have hcpos : 0 < c := div_pos (sub_pos.mpr hnu) hden
  have hcsmall : c < (1 / 8 : Real) := by
    apply (mul_lt_mul_iff_left₀ hden).mp
    nlinarith only [hrel]
  have hcxpos : 0 < c * x := mul_pos hcpos hxpos
  have hcx : c * x < (1 / 32 : Real) := by
    calc
      c * x < (1 / 8 : Real) * x := mul_lt_mul_of_pos_right hcsmall hxpos
      _ < (1 / 8 : Real) * (1 / 4 : Real) :=
        mul_lt_mul_of_pos_left hxquarter (by norm_num)
      _ = (1 / 32 : Real) := by norm_num
  have h1x : 0 < 1 - x := by linarith only [hxquarter]
  have htheta : (theta : Real) = (1 - x) ^ 2 := by
    simp only [theta, x, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]
  have hApos : 0 < A := by
    dsimp only [A]
    linarith only [hxquarter, hcx]
  have hAlt : A < 1 - x := by
    dsimp only [A]
    linarith only [hcxpos]
  have hAone : A < 1 := by linarith only [hAlt, hxpos]
  have hetaPos : 0 < eta := hcxpos
  have hetaLt : eta < 1 := by
    change c * x < 1
    linarith only [hcx]
  have hqLtOne : q < 1 := by
    have hreal : (q : Real) < ((1 : Rat) : Real) := by
      simpa only [Rat.cast_one] using (show x < 1 by linarith only [hxquarter])
    exact Rat.cast_lt.mp hreal
  have hthetaPos : 0 < theta := by
    have hbase : 0 < 1 - q := sub_pos.mpr hqLtOne
    exact pow_pos hbase 2
  have hqposQ : 0 < q := Rat.cast_pos.mp hqpos
  have hq2 : q ^ 2 < q := by
    nlinarith only [mul_lt_mul_of_pos_left hqLtOne hqposQ]
  have hthetaLt : theta < 1 := by
    dsimp only [theta]
    nlinarith only [hq2, hqposQ]
  have hAsq : A ^ 2 < (theta : Real) := by
    have hmul1 : A * A < (1 - x) * A :=
      mul_lt_mul_of_pos_right hAlt hApos
    have hmul2 : (1 - x) * A < (1 - x) * (1 - x) :=
      mul_lt_mul_of_pos_left hAlt h1x
    rw [htheta]
    nlinarith only [hmul1, hmul2]
  have hdenDet : 0 < 4 * (nu - 1) := by linarith only [hnu]
  have hprod : (nu - 1) * x < 3 * (nu - 2) / 4 := by
    have hmul := mul_lt_mul_of_pos_right hxdet hdenDet
    have hcancel :
        (3 * (nu - 2) / (4 * (nu - 1))) * (4 * (nu - 1)) = 3 * (nu - 2) :=
      div_mul_cancel₀ _ (ne_of_gt hdenDet)
    rw [hcancel] at hmul
    nlinarith only [hmul]
  have hlin : nu * (1 - 2 * c) - 2 = 3 * (nu - 2) / 4 := by
    nlinarith only [hrel]
  have hslack_formula :
      nu * (A * (1 - eta) - (theta : Real)) - (1 - (theta : Real)) =
        x * (3 * (nu - 2) / 4 + x * (1 - nu + nu * c + nu * c ^ 2)) := by
    rw [htheta]
    dsimp only [A, eta]
    calc
      nu * ((1 - x - c * x) * (1 - c * x) - (1 - x) ^ 2) -
          (1 - (1 - x) ^ 2) =
          x * (nu * (1 - 2 * c) - 2 + x * (nu * (c + c ^ 2 - 1) + 1)) := by ring
      _ = x * (3 * (nu - 2) / 4 + x * (1 - nu + nu * c + nu * c ^ 2)) := by
        rw [hlin]
        ring
  have hcoef : -(nu - 1) <= 1 - nu + nu * c + nu * c ^ 2 := by
    have h1 : 0 <= nu * c := le_of_lt (mul_pos hnu0 hcpos)
    have h2 : 0 <= nu * c ^ 2 := mul_nonneg (le_of_lt hnu0) (sq_nonneg c)
    linarith only [h1, h2]
  have hfactor : 0 < 3 * (nu - 2) / 4 + x * (1 - nu + nu * c + nu * c ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hxpos)
    nlinarith only [hmul, hprod]
  have hslack : 0 < nu * (A * (1 - eta) - (theta : Real)) - (1 - (theta : Real)) := by
    rw [hslack_formula]
    exact mul_pos hxpos hfactor
  refine Exists.intro theta (Exists.intro A (Exists.intro eta ?_))
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro rfl ?_
  refine And.intro hthetaPos ?_
  refine And.intro hthetaLt ?_
  refine And.intro hApos ?_
  refine And.intro hAone ?_
  refine And.intro hetaPos ?_
  refine And.intro hetaLt ?_
  exact And.intro hAsq hslack
