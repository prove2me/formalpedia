-- Prove2me | solution 1 for OAI.Erdos3.residueTruncationCap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:18:33.276988+00:00
-- url     : https://prove2.me/submissions/d37fa3ba-3775-4158-b5b5-be8239dfb7a3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueTruncationCap_nonneg (ι : Type*) [Fintype ι] [DecidableEq ι]
    (b : ℕ) {eta : ℝ} (heta : 0 ≤ eta) : 0 ≤ residueTruncationCap ι b eta := by
  unfold residueTruncationCap
  positivity

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.residueTruncationCap_nonneg.{u_1} := @OAI.Erdos3.residueTruncationCap_nonneg.{u_1}
