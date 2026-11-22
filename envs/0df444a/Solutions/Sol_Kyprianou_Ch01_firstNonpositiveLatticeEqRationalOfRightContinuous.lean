-- Prove2me | solution 1 for Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:37:51.687131+00:00
-- url     : https://prove2.me/submissions/1e8df588-5217-496a-98fe-5d1f2358e1ec

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
import Theorems.Thm_Kyprianou_Ch01_rationalFirstNonpositiveClockEqOfRightContinuous
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Original source first passage equals its rational lower clock. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    firstNonpositiveLattice X ω =
      ⨅ r : ℚ,
        if X (Real.toNNReal (r : ℝ)) ω ≤ 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  classical
  let E : Set ℝ≥0 := {t | X t ω ≤ 0}
  let S : Set (WithTop ℝ≥0) :=
    {z | ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = z ∧ X u ω ≤ 0}
  have him : S = (fun u : ℝ≥0 => (u : WithTop ℝ≥0)) '' E := by
    ext z
    constructor
    · rintro ⟨u, hu, hfu⟩
      exact ⟨u, hfu, hu⟩
    · rintro ⟨u, hfu, hu⟩
      exact ⟨u, hu, hfu⟩
  have hsource : firstNonpositiveLattice X ω = sInf S := by
    by_cases he : E.Nonempty
    · have hh : ∃ t : ℝ≥0, X t ω ≤ 0 := he
      have hco : ((sInf E : ℝ≥0) : WithTop ℝ≥0) = sInf S := by
        rw [him]
        exact WithTop.coe_sInf' he (by bddDefault : BddBelow E)
      change (if ∃ t : ℝ≥0, X t ω ≤ 0 then
        ((sInf {t : ℝ≥0 | X t ω ≤ 0} : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) = sInf S
      rw [if_pos hh]
      exact hco
    · have hempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
      have hh : ¬ ∃ t : ℝ≥0, X t ω ≤ 0 := by
        rintro ⟨t, ht⟩
        exact he ⟨t, ht⟩
      change (if ∃ t : ℝ≥0, X t ω ≤ 0 then
        ((sInf {t : ℝ≥0 | X t ω ≤ 0} : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) = sInf S
      rw [if_neg hh, him, hempty]
      simp only [Set.image_empty, sInf_empty]
  rw [hsource]
  exact Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous
    (fun t => X t ω) hright
