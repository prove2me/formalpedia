-- Prove2me | solution 1 for Leopoldt.closure_range_diagonalUnits_subset_unitClosure
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:23:25.166673+00:00
-- url     : https://prove2.me/submissions/8116fa58-4c4c-48b4-b11f-7a43f0714984

import Theorems.Thm_Leopoldt_isClosed_unitClosure

open Leopoldt in
theorem solution (p : ℕ) [Fact p.Prime] (K : Type*)
    [Field K] [NumberField K] :
    closure (Set.range (diagonalUnits p K)) ⊆ (unitClosure p K : Set (SemilocalUnits p K)) := by
  refine closure_minimal ?_ (isClosed_unitClosure p K)
  rintro _ ⟨e, rfl⟩
  exact Subgroup.mem_iInf.2 fun n => Subgroup.mem_sup_left ⟨e, rfl⟩
