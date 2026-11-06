-- Prove2me | solution 1 for Monodromy.Structure.conditional_gates_strictly_extend
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:24:04.197312+00:00
-- url     : https://prove2.me/submissions/f4a02549-d61a-486a-aeee-1ce4edbdcd03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Monodromy_Structure
import Theorems.Thm_Monodromy_Structure_continuation_characterization
import Theorems.Thm_Monodromy_Structure_no_probeFree_hardFunction

open Monodromy
open Monodromy.Structure
open CoupledContinuation NativeInterface

theorem solution :
    ∃ function : ℕ → Part ℕ, Realizable function ∧ ¬ ProbeFreeRealizable function := by
  refine ⟨ForwardBoundary.hardFunction, ?_, no_probeFree_hardFunction⟩
  apply (continuation_characterization _).2
  exact Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)
