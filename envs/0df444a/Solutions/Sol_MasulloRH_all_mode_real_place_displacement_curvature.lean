-- Prove2me | solution 1 for MasulloRH.all_mode_real_place_displacement_curvature
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:27:29.937205+00:00
-- url     : https://prove2.me/submissions/c0b57ceb-7efb-4871-8807-36d124a16440

import Mathlib
open Filter
open scoped Topology
theorem solution (M : ℝ) (c : ℕ → ℝ) (hc0 : c 0 = 0) :
    let a := fun n : ℕ => (1/2 : ℝ) + 2*n
    let B := fun z : ℝ => (z-5/2)*(z-3/2)*(z-1/2)*(z-1)*(z+1)
    (∀ n : ℕ, 1 ≤ n → M * B (a n) / 9 * (1/4 : ℝ)^n ≤ c n) →
    Summable (fun n => 2*(a n - 1)*c n) →
    HasSum (fun n : ℕ => 2*(a n-1)*B (a n)/9*(1/4 : ℝ)^n) (179864/243 : ℝ) ∧
      (1438669/1944 : ℝ)*M ≤ (∑' n : ℕ, 2*(a n-1)*c n) - M/8 := by
  intro a B hc hsum
  let p := fun n : ℕ => 2*(a n-1)*B (a n)/9 * (1/4 : ℝ)^n
  let Q := fun x : ℝ => (4608*x^6+3456*x^5+27936*x^4+82440*x^3+171828*x^2+249324*x+179864)/243
  let R := fun n : ℕ => Q n * (1/4 : ℝ)^n
  have recu (n : ℕ) : p n = R n - R (n+1) := by
    dsimp [p,R,Q,a,B]; rw [pow_succ]; push_cast; ring
  have init : R 0 = (179864/243:ℝ) := by norm_num [R,Q]
  have parts (N : ℕ) : ∑ n ∈ Finset.range N, p n = (179864/243 : ℝ)-R N := by
    induction N with
    | zero => simp [init]
    | succ n ih => rw [Finset.sum_range_succ,ih,recu n]; ring
  have geom (k : ℕ) (d : ℝ) :
      Tendsto (fun n : ℕ => d*((n:ℝ)^k*(1/4:ℝ)^n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := d)).mul
      (tendsto_pow_const_mul_const_pow_of_lt_one k (by norm_num : 0 ≤ (1/4 : ℝ)) (by norm_num))
  have rlim : Tendsto R atTop (𝓝 0) := by
    have H := ((((((geom 6 (4608/243)).add (geom 5 (3456/243))).add
      (geom 4 (27936/243))).add (geom 3 (82440/243))).add (geom 2 (171828/243))).add
      (geom 1 (249324/243))).add (geom 0 (179864/243))
    simp only [add_zero] at H
    apply H.congr'
    filter_upwards [] with n
    dsimp [R,Q]
    ring
  have pos (n : ℕ) : 0 ≤ p n := by
    rcases n with _|n
    · norm_num [p,a,B]
    rcases n with _|n
    · norm_num [p,a,B]
    have fact : p (n+1+1) = ((n:ℝ)+2)*(n+1)*(2*n+3)*(4*n+7)^2*(4*n+11)/9*(1/4:ℝ)^(n+1+1) := by
      dsimp [p,a,B]; push_cast; ring
    rw [fact]; positivity
  have exactSum : HasSum p (179864/243 : ℝ) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg pos _).mpr
    simp_rw [parts]
    simpa using (tendsto_const_nhds (x := (179864/243 : ℝ))).sub rlim
  refine ⟨exactSum,?_⟩
  have lower (n : ℕ) : M*p n ≤ 2*(a n-1)*c n := by
    rcases n with _|n
    · norm_num [p,a,B,hc0]
    have ha : 0 ≤ 2*(a (n+1)-1) := by dsimp [a]; push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith
    have := mul_le_mul_of_nonneg_left (hc (n+1) (by omega)) ha
    dsimp [p]
    linarith only [this]
  have lo := (exactSum.mul_left M).tsum_eq
  have le := (exactSum.mul_left M).summable.tsum_le_tsum lower hsum
  rw [lo] at le
  linarith
