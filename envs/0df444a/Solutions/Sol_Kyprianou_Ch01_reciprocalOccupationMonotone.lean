-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationMonotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:20:41.64347+00:00
-- url     : https://prove2.me/submissions/151a4903-6cc6-48bd-9753-a429b150a52f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reverse Lamperti occupation clock is monotone, including infinity. -/
theorem solution {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => reciprocalOccupation X t ω) := by
  intro a b hab
  unfold reciprocalOccupation
  apply lintegral_mono_set
  intro s hs
  exact ⟨hs.1, hs.2.trans (by exact_mod_cast hab)⟩
