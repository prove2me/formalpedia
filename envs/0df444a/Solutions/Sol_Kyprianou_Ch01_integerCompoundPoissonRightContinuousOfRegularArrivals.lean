-- Prove2me | solution 1 for Kyprianou.Ch01.integerCompoundPoissonRightContinuousOfRegularArrivals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:44:08.212207+00:00
-- url     : https://prove2.me/submissions/e42f529e-23c7-49d8-8bb2-92a48330edff

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Theorems.Thm_Kyprianou_Ch01_jumpCountLocalRightConstOfRegularArrival
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Zero-drift compound Poisson lattice paths are locally constant to the right. -/
theorem solution
    (y : ℕ) (T marks : ℕ → ℝ)
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          Int.floor ((y : ℝ) +
            ProbabilityTheory.piecewisePath 0 0 T marks (s : ℝ)))
        (Set.Ici t) t := by
  intro t
  obtain ⟨c, hgt, hcount⟩ :=
    Kyprianou.Ch01.jumpCountLocalRightConstOfRegularArrival
      T hmono htop t
  have heqOn : Set.EqOn
      (fun s : ℝ≥0 =>
        Int.floor ((y : ℝ) +
          ProbabilityTheory.piecewisePath 0 0 T marks (s : ℝ)))
      (fun _ : ℝ≥0 =>
        Int.floor ((y : ℝ) +
          ProbabilityTheory.piecewisePath 0 0 T marks (t : ℝ)))
      (Ico t c) := by
    intro s hs
    change Int.floor ((y : ℝ) +
        ((0 : ℝ) + 0 * (s : ℝ) +
          ∑ i ∈ Finset.range
            (ProbabilityTheory.jumpCount T (s : ℝ)), marks i)) =
      Int.floor ((y : ℝ) +
        ((0 : ℝ) + 0 * (t : ℝ) +
          ∑ i ∈ Finset.range
            (ProbabilityTheory.jumpCount T (t : ℝ)), marks i))
    rw [hcount s hs]
    simp
  have hmem : Ico t c ∈ 𝓝[Ici t] t := by
    rw [← Set.Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hgt)
  have hgc : ContinuousWithinAt
      (fun _ : ℝ≥0 =>
        Int.floor ((y : ℝ) +
          ProbabilityTheory.piecewisePath 0 0 T marks (t : ℝ)))
      (Ici t) t := continuousWithinAt_const
  refine hgc.congr_of_eventuallyEq
    (Filter.eventually_of_mem hmem fun s hs => heqOn hs) ?_
  exact heqOn (Set.left_mem_Ico.mpr hgt)
