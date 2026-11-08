-- Prove2me | solution 1 for MultimodularDocks.depot_multimodular
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:44:36.913219+00:00
-- url     : https://prove2.me/submissions/e7feeb12-8056-43e0-9312-c79be22578a5

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular
import Definitions.Def_MultimodularDocks_depotCost

open MultimodularDocks in
theorem solution (B : ℤ) : IsMultimodular (depotCost B) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro d b _ _ <;> simp only [depotCost] <;> push_cast <;> linarith
