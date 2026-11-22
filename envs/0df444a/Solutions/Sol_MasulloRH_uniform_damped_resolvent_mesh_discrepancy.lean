-- Prove2me | solution 1 for MasulloRH.uniform_damped_resolvent_mesh_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:43:50.780938+00:00
-- url     : https://prove2.me/submissions/11e16670-513e-4694-ab8d-48515da19455

import Mathlib
open Finset MeasureTheory
theorem solution (n : ℕ) (u A : ℕ → ℝ) (c d ε : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d) (he : 0 ≤ ε)
    (hu : Monotone u) (hu0 : u 0 = 0) (hu1 : u n = 1) (hA : A 0 = 0)
    (hm : ∀ i < n, u (i+1) - u i ≤ d)
    (hD : ∀ i ≤ n, |A i - (u i)^2/2| ≤ ε) :
    |(∑ i ∈ range n, Real.exp (-c * u (i+1)) * (A (i+1) - A i)) -
      (1-(1+c)*Real.exp (-c))/c^2| ≤ ε+d := by
  let w := fun x : ℝ => Real.exp (-c*x)
  let F := fun x : ℝ => (1-(1+c*x)*Real.exp (-c*x))/c^2
  let E := fun i : ℕ => A i - (u i)^2/2
  let B := fun j : ℕ => (∑ i ∈ range j, w (u (i+1))*(A (i+1)-A i)) -
    F (u j) - w (u j)*E j
  have w0 : w 0 = 1 := by simp [w]
  have wpos (x : ℝ) : 0 ≤ w x := (Real.exp_pos _).le
  have wm : Antitone w := fun x y hxy =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr hc.le))
  have hu_nn (i : ℕ) : 0 ≤ u i := by simpa [hu0] using (hu (Nat.zero_le i))
  have der (x : ℝ) : HasDerivAt F (x*w x) x := by
    have h₁ := (hasDerivAt_const x (-c)).mul (hasDerivAt_id x)
    have h₂ := (hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_const x c).mul (hasDerivAt_id x))
    have hx := ((hasDerivAt_const x (1:ℝ)).sub (h₂.mul h₁.exp)).div_const (c^2)
    convert hx using 1 <;> (try dsimp [F,w,id]) <;> first | rfl | (field_simp [hc.ne']; ring)
  have cell (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      w b * ((b^2-a^2)/2) ≤ F b - F a ∧ F b - F a ≤ w a * ((b^2-a^2)/2) := by
    have cint (v : ℝ) : (∫ x in a..b, v*x) = v*((b^2-a^2)/2) := by
      have dv (x : ℝ) : HasDerivAt (fun y : ℝ => v*y^2/2) (v*x) x := by
        have hx := (((hasDerivAt_const x v).mul ((hasDerivAt_id x).pow 2)).div_const 2)
        convert hx using 1 <;> first | rfl | (simp [id] <;> ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => dv x)
        ((continuous_const.mul continuous_id).intervalIntegrable _ _)]
      ring
    have cont : Continuous (fun x : ℝ => x*w x) := by dsimp [w]; fun_prop
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
      (fun x _ => der x) (cont.intervalIntegrable _ _)
    rw [← eq, ← cint, ← cint]
    constructor
    · exact intervalIntegral.integral_mono_on hab
        ((continuous_const.mul continuous_id).intervalIntegrable _ _) (cont.intervalIntegrable _ _)
        (fun x hx => by simpa [mul_comm] using mul_le_mul_of_nonneg_right (wm hx.2) (ha.trans hx.1))
    · exact intervalIntegral.integral_mono_on hab (cont.intervalIntegrable _ _)
        ((continuous_const.mul continuous_id).intervalIntegrable _ _)
        (fun x hx => by simpa [mul_comm] using mul_le_mul_of_nonneg_right (wm hx.1) (ha.trans hx.1))
  have bound (j : ℕ) (hj : j ≤ n) : |B j| ≤ (ε+d)*(1-w (u j)) := by
    induction j with
    | zero => simp [B,E,F,w,hu0,hA]
    | succ i ih =>
      have hi : i < n := by omega
      have hxy : u i ≤ u (i+1) := hu (Nat.le_succ _)
      have hbw : 0 ≤ w (u i)-w (u (i+1)) := sub_nonneg.mpr (wm hxy)
      have hy1 : u (i+1) ≤ 1 := by simpa [hu1] using hu hj
      have hinc : ((u (i+1))^2-(u i)^2)/2 ≤ d := by
        have h := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2-u (i+1)-u i by linarith)
        linarith [hm i hi]
      have hcell := cell _ _ (hu_nn i) hxy
      let W := w (u i)-w (u (i+1))
      let D := F (u (i+1))-F (u i) - w (u (i+1))*(((u (i+1))^2-(u i)^2)/2)
      have hD0 : 0 ≤ D := sub_nonneg.mpr hcell.1
      have hD1 : D ≤ W*d := by
        have hh := mul_le_mul_of_nonneg_left hinc hbw
        dsimp [D,W]; nlinarith [hcell.2]
      have hE : |E i| ≤ ε := hD i hi.le
      have hrec : B (i+1) = B i + W*E i - D := by
        dsimp [B,E,W,D]; rw [sum_range_succ]; ring
      rw [hrec]
      calc
        |B i + W*E i - D| ≤ |B i+W*E i| + |D| := abs_sub _ _
        _ ≤ (|B i| + |W*E i|) + |D| := by gcongr; exact abs_add_le _ _
        _ = (|B i|+ W*|E i|)+D := by rw [abs_mul,abs_of_nonneg hbw,abs_of_nonneg hD0]
        _ ≤ ((ε+d)*(1-w (u i))+W*ε) + W*d :=
          add_le_add (add_le_add (ih hi.le) (mul_le_mul_of_nonneg_left hE hbw)) hD1
        _ = _ := by dsimp [W]; ring
  have h := abs_add_le (B n) (w (u n)*E n)
  have hh := add_le_add (bound n le_rfl) (mul_le_mul_of_nonneg_left (hD n le_rfl) (wpos (u n)))
  have hn : B n + w (u n)*E n =
      (∑ i ∈ range n, w (u (i+1))*(A (i+1)-A i)) -F (u n) := by dsimp [B]; ring
  rw [hn,abs_mul,abs_of_nonneg (wpos _)] at h
  have hh' := h.trans hh
  have hlast := mul_nonneg hd (wpos (u n))
  have goal : |(∑ i ∈ range n, w (u (i+1))*(A (i+1)-A i)) -F (u n)| ≤ ε+d := by nlinarith
  simpa [F,w,hu1] using goal
