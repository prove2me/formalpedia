-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineGridCompactBoundLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:28.206805+00:00
-- url     : https://prove2.me/submissions/c1efa626-3a0b-42c4-b3dc-660c6729a08c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteAffineGridIntegralLimitV1
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

/-- Only a compact-horizon bound is required for the finite affine grid theorem. -/
theorem solution (T : NNReal) (S : Finset NNReal) (j H Y : NNReal → ℝ) (b C : ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0)
    (hH : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r)))
    (hC : 0 ≤ C) (hb : ∀ r ≤ T, |H r| ≤ C) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      let u := T * (i : NNReal) / (n : NNReal)
      let v := T * ((i+1 : ℕ) : NNReal) / (n : NNReal)
      H u * (Y v - Y u)) atTop
      (𝓝 (b * (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal) +
        ∑ r ∈ S, j r * H r)) := by
  let G := fun r => min C (max (-C) (H r))
  have hG (r : NNReal) : |G r| ≤ C := by
    rw [abs_le]
    exact ⟨le_min (by linarith) (le_max_left _ _),min_le_left _ _⟩
  have hEq (r : NNReal) (hr : r ≤ T) : G r = H r := by
    have h := abs_le.mp (hb r hr)
    simp [G,max_eq_right h.1,min_eq_right h.2]
  have hcont (r : NNReal) (hr : 0 < r) : Tendsto G (𝓝[<] r) (𝓝 (G r)) :=
    tendsto_const_nhds.min (tendsto_const_nhds.max (hH r hr))
  have h := Kyprianou.Ch04.finiteAffineGridIntegralLimitV1 T S j G Y b C hS hY hcont hG
  have hI : (∫ s in Icc (0 : ℝ) (T : ℝ), G s.toNNReal) =
      ∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact hEq _ (Real.toNNReal_le_iff_le_coe.mpr hs.2)
  have hJ : (∑ r ∈ S, j r * G r) = ∑ r ∈ S, j r * H r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hEq _ (hS r hr).2]
  rw [hI,hJ] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
  have hu : T * (i : NNReal) / (n : NNReal) ≤ T := by
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    gcongr
  dsimp only
  rw [hEq _ hu]
