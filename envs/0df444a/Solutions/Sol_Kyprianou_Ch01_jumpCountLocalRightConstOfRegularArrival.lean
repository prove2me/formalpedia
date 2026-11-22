-- Prove2me | solution 1 for Kyprianou.Ch01.jumpCountLocalRightConstOfRegularArrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:48:59.768169+00:00
-- url     : https://prove2.me/submissions/0a25b5ef-185b-442e-bb58-7d5e95565dbe

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_sourceJumpCountMonotoneAndLtIffPublic
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite-time jump count stays constant up to its next arrival. -/
theorem solution
    (T : ℕ → ℝ) (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) (t : ℝ≥0) :
    ∃ c : ℝ≥0, t < c ∧
      ∀ s ∈ Set.Ico t c,
        ProbabilityTheory.jumpCount T (s : ℝ) =
        ProbabilityTheory.jumpCount T (t : ℝ) := by
  let N : ℝ → ℕ := ProbabilityTheory.jumpCount T
  obtain ⟨hIff0, hMon0⟩ :=
    Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic T hmono htop
  have hNmon : Monotone N := hMon0
  have hNiff : ∀ n : ℕ, ∀ u : ℝ, n < N u ↔ T n ≤ u := hIff0
  have hne : ({n : ℕ | (t : ℝ) < T n}).Nonempty :=
    (htop.eventually_gt_atTop (t : ℝ)).exists
  have hnext : (t : ℝ) < T (N (t : ℝ)) := by
    change (t : ℝ) < T (sInf {n : ℕ | (t : ℝ) < T n})
    exact Nat.sInf_mem hne
  have hcount : ∀ u ∈ Ico (t : ℝ) (T (N (t : ℝ))),
      N u = N (t : ℝ) := by
    intro u hu
    have hl : N (t : ℝ) ≤ N u := hNmon hu.1
    have hr : N u ≤ N (t : ℝ) := by
      by_contra hh
      have hhit : T (N (t : ℝ)) ≤ u :=
        (hNiff (N (t : ℝ)) u).mp (by omega)
      exact (not_le.mpr hu.2) hhit
    omega
  have hnonneg : 0 ≤ T (N (t : ℝ)) :=
    (NNReal.coe_nonneg t).trans hnext.le
  let c : ℝ≥0 := Real.toNNReal (T (N (t : ℝ)))
  have hc : (c : ℝ) = T (N (t : ℝ)) :=
    Real.coe_toNNReal _ hnonneg
  have hgt : t < c := by
    exact_mod_cast (show (t : ℝ) < (c : ℝ) by simpa only [hc] using hnext)
  refine ⟨c, hgt, ?_⟩
  intro s hs
  change N (s : ℝ) = N (t : ℝ)
  apply hcount
  constructor
  · exact_mod_cast hs.1
  · have hs' : (s : ℝ) < (c : ℝ) := by exact_mod_cast hs.2
    simpa only [hc] using hs'
