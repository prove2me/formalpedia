-- Prove2me | solution 1 for OAI.Erdos3.affineFinalDegree_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:49:43.017155+00:00
-- url     : https://prove2.me/submissions/8c5f97cc-a7fd-4e40-b488-facd1e04e59e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AffineDegreeChoice
namespace OAI

section

namespace Erdos3

theorem affineFinalDegree_bounds (j r : ℕ) (shell Q : ℝ) :
    j + r ≤ affineFinalDegree j r shell Q ∧
    j + CyclicCrootSisask.spectralIterations shell Q ≤ affineFinalDegree j r shell Q := by
  unfold affineFinalDegree
  omega

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.affineFinalDegree_bounds := @OAI.Erdos3.affineFinalDegree_bounds
