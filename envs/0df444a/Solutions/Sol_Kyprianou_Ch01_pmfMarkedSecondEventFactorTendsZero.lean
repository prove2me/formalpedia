-- Prove2me | solution 1 for Kyprianou.Ch01.pmfMarkedSecondEventFactorTendsZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:15:12.549963+00:00
-- url     : https://prove2.me/submissions/bce75538-482c-4e27-bafe-6739fcc3d2d9

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_pmfWeightedTanneryRightAtZero
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (p : PMF ℕ) (rate : ℝ≥0) (y : ℕ) :
    Tendsto
      (fun t : ℝ => ∑' k : ℕ, (p k).toReal *
        (1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  let F : ℝ → ℕ → ℝ := fun t k =>
    1 - Real.exp (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t))
  have hpoint (k : ℕ) :
      Tendsto (fun t : ℝ => F t k)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : ContinuousAt
        (fun t : ℝ => 1 - Real.exp
          (-((rate : ℝ) * (((y + k : ℕ) : ℝ)) * t))) 0 := by
      fun_prop
    simpa [F] using (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have hbound : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ k : ℕ, |F t k| ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have hr : 0 ≤ (rate : ℝ) := rate.property
    have hz : 0 ≤ (rate : ℝ) * (((y + k : ℕ) : ℝ)) * t :=
      mul_nonneg (mul_nonneg hr (Nat.cast_nonneg _)) ht.le
    have he : Real.exp (-((rate : ℝ) *
          (((y + k : ℕ) : ℝ)) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)
    have he0 : 0 ≤ Real.exp (-((rate : ℝ) *
        (((y + k : ℕ) : ℝ)) * t)) :=
      (Real.exp_pos _).le
    dsimp [F]
    rw [abs_of_nonneg (by linarith)]
    linarith
  exact Kyprianou.Ch01.pmfWeightedTanneryRightAtZero
    p F hpoint hbound
