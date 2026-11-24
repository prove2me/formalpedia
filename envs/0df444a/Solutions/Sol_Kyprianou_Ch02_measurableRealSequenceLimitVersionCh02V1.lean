-- Prove2me | solution 1 for Kyprianou.Ch02.measurableRealSequenceLimitVersionCh02V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:37:13.316619+00:00
-- url     : https://prove2.me/submissions/996fb64c-059b-4fbe-82f3-810390fca916

import Mathlib
open MeasureTheory Filter Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) :
    ∃ g : Ω → ℝ, Measurable g ∧
      ∀ ω l, Tendsto (fun n => F n ω) atTop (nhds l) → g ω = l := by
  classical
  let A : Set Ω := {ω | ∃ l : ℝ, Tendsto (fun n => F n ω) atTop (nhds l)}
  have hA : MeasurableSet A :=
    MeasureTheory.measurableSet_exists_tendsto (l := atTop) hF
  let g : Ω → ℝ := fun ω => if h : ω ∈ A then h.choose else 0
  have hg : Tendsto (fun n => A.indicator (F n)) atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro ω
    by_cases h : ω ∈ A
    · simpa [g, h, Set.indicator_of_mem h] using h.choose_spec
    · simpa [g, h, Set.indicator_of_notMem h] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  refine ⟨g, measurable_of_tendsto_metrizable (fun n => (hF n).indicator hA) hg, ?_⟩
  intro ω l hl
  have h : ω ∈ A := ⟨l, hl⟩
  have hlim := h.choose_spec
  change (if hh : ω ∈ A then hh.choose else 0) = l
  rw [dif_pos h]
  exact tendsto_nhds_unique hlim hl
