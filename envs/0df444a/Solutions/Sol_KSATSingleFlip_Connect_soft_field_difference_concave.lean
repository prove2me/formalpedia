-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_difference_concave
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:19:05.368837+00:00
-- url     : https://prove2.me/submissions/a2945541-72fb-4f76-9503-eaea07fc0df4

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
noncomputable section
open KSATSingleFlip.Connect Set

private def d1 (x : ℝ) : ℝ :=
  (1-2*x)/Real.sqrt (x*(1-x)) - 1/Real.sqrt x + 1/Real.sqrt (1-x)
private def d2 (x : ℝ) : ℝ :=
  -(1/(2*(Real.sqrt (x*(1-x)))^3)) + 1/(2*(Real.sqrt x)^3) + 1/(2*(Real.sqrt (1-x))^3)

private theorem deriv1 (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => fW x-gW x) (d1 x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy : 0 < 1-x := by linarith
  have hy0 : 1-x ≠ 0 := ne_of_gt hy
  have hz : 0 < x*(1-x) := mul_pos hx hy
  have hz0 : x*(1-x) ≠ 0 := ne_of_gt hz
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsy : Real.sqrt (1-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hsz : Real.sqrt (x*(1-x)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hz)
  have hA := ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))).sqrt hz0
  have hB := (hasDerivAt_id x).sqrt hx0
  have hC := ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).sqrt hy0
  have hD := ((hA.sub hB).sub hC).add_const 1
  have hD2 := hD.const_mul 2
  have hD2' : HasDerivAt (fun y : ℝ => 2*(Real.sqrt (y*(1-y))-Real.sqrt y-Real.sqrt (1-y)+1))
      (2*((1*(1-x)+x*(0-1))/(2*Real.sqrt (x*(1-x))) - 1/(2*Real.sqrt x) - (0-1)/(2*Real.sqrt (1-x)))) x := by
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq] using hD2
  have heqfun : (fun y : ℝ => 2*(Real.sqrt (y*(1-y))-Real.sqrt y-Real.sqrt (1-y)+1)) =
      (fun y => fW y-gW y) := by
    funext y
    simp only [fW,gW]
    ring
  have heqcoeff : 2*((1*(1-x)+x*(0-1))/(2*Real.sqrt (x*(1-x))) - 1/(2*Real.sqrt x) - (0-1)/(2*Real.sqrt (1-x))) = d1 x := by
    dsimp [d1]
    field_simp
    ring
  rw [heqfun,heqcoeff] at hD2'
  exact hD2'

private theorem deriv2 (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : HasDerivAt d1 (d2 x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy : 0 < 1-x := by linarith
  have hy0 : 1-x ≠ 0 := ne_of_gt hy
  have hz : 0 < x*(1-x) := mul_pos hx hy
  have hz0 : x*(1-x) ≠ 0 := ne_of_gt hz
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsy : Real.sqrt (1-x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hy)
  have hsz : Real.sqrt (x*(1-x)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hz)
  have hsx2 : (Real.sqrt x)^2 = x := Real.sq_sqrt (le_of_lt hx)
  have hsy2 : (Real.sqrt (1-x))^2 = 1-x := Real.sq_sqrt (le_of_lt hy)
  have hsz2 : (Real.sqrt (x*(1-x)))^2 = x*(1-x) := Real.sq_sqrt (le_of_lt hz)
  have hA0 := ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))).sqrt hz0
  have hA : HasDerivAt (fun y : ℝ => Real.sqrt (y*(1-y))) ((1-2*x)/(2*Real.sqrt (x*(1-x)))) x := by
    have hcoeff : (1*(1-x)+x*(0-1))/(2*Real.sqrt (x*(1-x))) = (1-2*x)/(2*Real.sqrt (x*(1-x))) := by ring
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, hcoeff] using hA0
  have hB : HasDerivAt (fun y : ℝ => Real.sqrt y) (1/(2*Real.sqrt x)) x := by
    simpa using (hasDerivAt_id x).sqrt hx0
  have hC : HasDerivAt (fun y : ℝ => Real.sqrt (1-y)) (-1/(2*Real.sqrt (1-x))) x := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div] using ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).sqrt hy0
  have hnum : HasDerivAt (fun y : ℝ => 1-2*y) (-2) x := by
    have hnum' := (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul 2)
    change HasDerivAt (fun y : ℝ => 1-2*y) (0-2*1) x at hnum'
    simpa using hnum'
  have h1 := hnum.div hA hsz
  have h2 := (hasDerivAt_const x (1:ℝ)).div hB hsx
  have h3 := (hasDerivAt_const x (1:ℝ)).div hC hsy
  have hall := (h1.sub h2).add h3
  change HasDerivAt d1 _ x at hall
  apply hall.congr_deriv
  dsimp [d2]
  have hid : 4*(Real.sqrt (x*(1-x)))^2 + (1-2*x)^2 = 1 := by rw [hsz2]; ring
  have hmul := congrArg (fun v : ℝ => v*(Real.sqrt x)^3*(Real.sqrt (1-x))^3) hid
  field_simp
  nlinarith [hmul]

private theorem d2_nonpos (x : ℝ) (hx : 0 < x) (hx1 : x < 1) : d2 x ≤ 0 := by
  have hy : 0 < 1-x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (1-x) := Real.sqrt_pos.mpr hy
  have hs1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr (le_of_lt hx1)
  have ht1 : Real.sqrt (1-x) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hs2 : (Real.sqrt x)^2 = x := Real.sq_sqrt (le_of_lt hx)
  have ht2 : (Real.sqrt (1-x))^2 = 1-x := Real.sq_sqrt (le_of_lt hy)
  have hcube1 : (Real.sqrt x)^3 ≤ (Real.sqrt x)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt x)) (show 0 ≤ 1-Real.sqrt x by linarith)]
  have hcube2 : (Real.sqrt (1-x))^3 ≤ (Real.sqrt (1-x))^2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sqrt (1-x))) (show 0 ≤ 1-Real.sqrt (1-x) by linarith)]
  have hn : (Real.sqrt x)^3+(Real.sqrt (1-x))^3-1 ≤ 0 := by linarith
  have hd : 0 < 2*(Real.sqrt x)^3*(Real.sqrt (1-x))^3 := by positivity
  have hform : d2 x = ((Real.sqrt x)^3+(Real.sqrt (1-x))^3-1)/(2*(Real.sqrt x)^3*(Real.sqrt (1-x))^3) := by
    dsimp [d2]
    rw [Real.sqrt_mul (le_of_lt hx)]
    have hs0 : Real.sqrt x ≠ 0 := ne_of_gt hs
    have ht0 : Real.sqrt (1-x) ≠ 0 := ne_of_gt ht
    field_simp
    ring
  rw [hform]
  exact div_nonpos_of_nonpos_of_nonneg hn (le_of_lt hd)

theorem solution : ConcaveOn ℝ (Icc 0 1) (fun x => fW x-gW x) ∧
    (fW 0-gW 0 = 0) ∧ (fW 1-gW 1 = 0) := by
  constructor
  · apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := d1) (f'' := d2) (convex_Icc 0 1)
    · have hc : Continuous (fun x => fW x-gW x) := by unfold fW gW; fun_prop
      exact hc.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (deriv1 x hx.1 hx.2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (deriv2 x hx.1 hx.2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact d2_nonpos x hx.1 hx.2
  · simp [fW,gW]
