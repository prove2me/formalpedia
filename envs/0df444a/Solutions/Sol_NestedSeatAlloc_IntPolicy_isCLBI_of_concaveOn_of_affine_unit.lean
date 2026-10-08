-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.isCLBI_of_concaveOn_of_affine_unit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:42:49.634979+00:00
-- url     : https://prove2.me/submissions/472dca43-a410-4da3-ac79-14c47ae40639

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution
    {g : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Ici 0) g)
    (haff : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) (m + 1), g s = a + b * s) :
    IsCLBI g := by
  exact ⟨hconc, haff⟩
