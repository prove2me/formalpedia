-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ce_bad_first_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:10:57.630273+00:00
-- url     : https://prove2.me/submissions/e08bed4d-8152-446d-a959-2e2fb0ed1303

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The erroneous initial left value gives a nonvanishing stopped first-cell remainder. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    let X : NNReal → ℕ → ℝ := fun t _ => (t : ℝ)
    let Y : NNReal → ℕ → ℝ := fun t w => if t = 0 then (w : ℝ) else (t : ℝ)
    let f : ℝ × ℝ → ℝ := fun z => z.2 ^ 2
    let t : NNReal := 1 / (n : NNReal)
    let u : ℕ → NNReal := fun k => (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    t ≤ 1 ∧ 1 ≤ |∑ k ∈ Finset.range n,
      (f ((v k : ℝ), X (v (k+1)) n) - f ((v k : ℝ), X (v k) n) -
        fderiv ℝ f ((u k : ℝ),Y (u k) n) (0,1) *
          (X (v (k+1)) n - X (v k) n))| := by
  intro X Y f t u v
  have hn' : (1 : NNReal) ≤ n := by exact_mod_cast hn
  have ht : t ≤ 1 := (div_le_one (by positivity)).mpr hn'
  have h0 : v 0 = 0 := by simp [v,u]
  have hv (k : ℕ) (hk : 0 < k) : v k = t := by
    apply min_eq_left
    exact div_le_div_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  have hd : fderiv ℝ f (0,(n : ℝ)) (0,1) = 2*(n : ℝ) := by
    change fderiv ℝ (fun z : ℝ × ℝ => z.2 ^ 2) (0,(n : ℝ)) (0,1) = _
    rw [fderiv_fun_pow 2 (by fun_prop), fderiv_snd]
    simp
  let A : ℕ → ℝ := fun k =>
    f ((v k : ℝ), X (v (k+1)) n) - f ((v k : ℝ), X (v k) n) -
      fderiv ℝ f ((u k : ℝ),Y (u k) n) (0,1) * (X (v (k+1)) n - X (v k) n)
  refine ⟨ht,?_⟩
  change 1 ≤ |∑ k ∈ Finset.range n, A k|
  rw [Finset.sum_eq_single 0]
  · have hA : A 0 = (t : ℝ)^2 - 2*(n : ℝ)*(t : ℝ) := by
      simp [A,h0,hv 1 (by decide),u,X,Y,f,hd]
    rw [hA]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hmul : (n : ℝ) * (t : ℝ) = 1 := by
      simp [t, hn0]
    have htr : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
    rw [mul_assoc,hmul,mul_one]
    have hsq : (t : ℝ)^2 ≤ 1 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr htr)]
    exact (le_abs.mpr (Or.inr (by linarith)))
  · intro k hk hk0
    have hk' : 0 < k := Nat.pos_of_ne_zero hk0
    simp [A,hv k hk',hv (k+1) (Nat.succ_pos _)]
  · intro h
    exact (h (Finset.mem_range.mpr hn)).elim
