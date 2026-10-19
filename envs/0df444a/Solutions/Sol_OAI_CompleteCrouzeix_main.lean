-- Prove2me | solution 1 for OAI.CompleteCrouzeix.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:15:14.953655+00:00
-- url     : https://prove2.me/submissions/6725c635-36be-4e30-a84b-44e50ef795b4

import Mathlib
import Definitions.Def_CompleteCrouzeix
import Theorems.Thm_OAI_DirectCrouzeix_complete_crouzeix
import Theorems.Thm_OAI_DirectCrouzeix_uniform_sharpness

namespace OAI.CompleteCrouzeix

theorem main_from_direct : UniversalBound 2 ∧ ∀ C : ℝ, UniversalBound C → 2 ≤ C :=
  ⟨OAI.DirectCrouzeix.complete_crouzeix, fun C hC => OAI.DirectCrouzeix.uniform_sharpness C hC⟩

end OAI.CompleteCrouzeix

theorem solution : type_of% @OAI.CompleteCrouzeix.main_from_direct := @OAI.CompleteCrouzeix.main_from_direct
