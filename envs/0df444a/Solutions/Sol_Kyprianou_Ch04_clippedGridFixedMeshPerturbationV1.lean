-- Prove2me | solution 1 for Kyprianou.Ch04.clippedGridFixedMeshPerturbationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:31:48.241431+00:00
-- url     : https://prove2.me/submissions/eff80251-ab29-441e-8423-f56f8bc402e4

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- At a fixed finite mesh, uniform state and coefficient errors give a
deterministic uniform grid-sum perturbation bound. -/
theorem solution (Y Z H L : NNReal → ℝ) (T : NNReal) (u : ℕ → NNReal) (n : ℕ)
    (K B d e : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hd : 0 ≤ d) (he : 0 ≤ e)
    (hY : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hZ : ∀ t ≤ T, |Z t| ≤ B)
    (hH : ∀ k ∈ Finset.range n, |H (u k)| ≤ K)
    (hL : ∀ k ∈ Finset.range n, |H (u k) - L (u k)| ≤ e) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n, H (u k) *
      (Y (min t (u (k+1))) - Y (min t (u k)))) -
      (∑ k ∈ Finset.range n, L (u k) *
      (Z (min t (u (k+1))) - Z (min t (u k))))| ≤
        (n : ℝ) * (2*K*d + 2*B*e) := by
  intro t ht
  let v := fun k => min t (u k)
  have hv (k : ℕ) : v k ≤ T := (min_le_left _ _).trans ht
  have hdiff (k : ℕ) : |(Y (v (k+1)) - Y (v k)) -
      (Z (v (k+1)) - Z (v k))| ≤ 2*d := by
    rw [show (Y (v (k+1)) - Y (v k)) - (Z (v (k+1)) - Z (v k)) =
      (Y (v (k+1))-Z (v (k+1))) - (Y (v k)-Z (v k)) by ring]
    linarith [abs_sub (Y (v (k+1))-Z (v (k+1))) (Y (v k)-Z (v k)),
      hY _ (hv (k+1)),hY _ (hv k)]
  have hz (k : ℕ) : |Z (v (k+1)) - Z (v k)| ≤ 2*B := by
    linarith [abs_sub (Z (v (k+1))) (Z (v k)),hZ _ (hv (k+1)),hZ _ (hv k)]
  change |(∑ k ∈ Finset.range n,H (u k)*(Y (v (k+1))-Y (v k))) -
    (∑ k ∈ Finset.range n,L (u k)*(Z (v (k+1))-Z (v k)))| ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range n, (2*K*d + 2*B*e) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [show H (u k)*(Y (v (k+1))-Y (v k)) - L (u k)*(Z (v (k+1))-Z (v k)) =
        H (u k)*((Y (v (k+1))-Y (v k))-(Z (v (k+1))-Z (v k))) +
          (H (u k)-L (u k))*(Z (v (k+1))-Z (v k)) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul,abs_mul]
      have ha := mul_le_mul (hH k hk) (hdiff k) (abs_nonneg _) hK
      have hb := mul_le_mul (hL k hk) (hz k) (abs_nonneg _) he
      nlinarith
    _ = _ := by simp <;> ring
