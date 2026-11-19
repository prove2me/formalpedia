-- Prove2me | solution 1 for Kyprianou.Ch01.rationalStrictInf_le_firstUpperPassageContinuousPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:52:41.002294+00:00
-- url     : https://prove2.me/submissions/40a99318-cbd6-4948-aa6d-7e99f481fb2c

import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_rationalUpperCrossingBeforeAnyLaterTimePublic
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Positive rational strict crossing ensures the rational infimum is finite. -/
private theorem finiteFirstUpperHasRationalCrossing
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω))
    (hy : firstUpperPassage X s ω < (⊤ : WithTop ℝ≥0)) :
    (⨅ a : ℚ,
      if (0 < (a : ℝ) ∧ s < X (Real.toNNReal (a : ℝ)) ω)
        then ((Real.toNNReal (a : ℝ)) : WithTop ℝ≥0)
        else ⊤) < (⊤ : WithTop ℝ≥0) := by
  classical
  cases hpass : firstUpperPassage X s ω with
  | top =>
      simp [hpass] at hy
  | coe u =>
      have hut : firstUpperPassage X s ω <
          (((u + 1 : ℝ≥0)) : WithTop ℝ≥0) := by
        rw [hpass]
        exact WithTop.coe_lt_coe.mpr
          (lt_add_of_pos_right u one_pos)
      obtain ⟨r, hr, hrlt, hval⟩ :=
        rationalUpperCrossingBeforeAnyLaterTimePublic
          X ω s hContinuous (u + 1) hut
      calc
        (⨅ a : ℚ,
            if (0 < (a : ℝ) ∧ s < X (Real.toNNReal (a : ℝ)) ω)
              then ((Real.toNNReal (a : ℝ)) : WithTop ℝ≥0)
              else ⊤) ≤
          (if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
            then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
            else ⊤) := iInf_le _ r
        _ = ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0) := by
          simp [hr, hval] <;> rfl
        _ < (⊤ : WithTop ℝ≥0) := WithTop.coe_lt_top _

/-- Dense rational observations detect each finite time later than a first crossing. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω)) :
    (⨅ r : ℚ,
      if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
        then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
        else ⊤) ≤ firstUpperPassage X s ω := by
  classical
  refine le_of_forall_gt (fun (y : WithTop ℝ≥0) hy => ?_)
  cases y with
  | top =>
      exact finiteFirstUpperHasRationalCrossing X ω s hContinuous hy
  | coe t =>
      obtain ⟨r, hr, hrlt, hval⟩ :=
        rationalUpperCrossingBeforeAnyLaterTimePublic
          X ω s hContinuous t hy
      calc
        (⨅ a : ℚ,
            if (0 < (a : ℝ) ∧ s < X (Real.toNNReal (a : ℝ)) ω)
              then ((Real.toNNReal (a : ℝ)) : WithTop ℝ≥0)
              else ⊤) ≤
          (if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
            then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
            else ⊤) := iInf_le _ r
        _ = ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0) := by
          simp [hr, hval] <;> rfl
        _ < (t : WithTop ℝ≥0) :=
          WithTop.coe_lt_coe.mpr hrlt
