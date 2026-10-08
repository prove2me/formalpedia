-- Prove2me | solution 1 for OAI.Erdos3.translatedIntegerBox_eq_piFinset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:32:36.100591+00:00
-- url     : https://prove2.me/submissions/c0c0f556-ac1b-47b7-9551-8c50a2fbb402

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B008

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem translatedIntegerBox_eq_piFinset (lo : I → ℤ) (N : I → ℕ) :
    translatedIntegerBox lo N = Fintype.piFinset (fun i => Finset.Ico (lo i) (lo i + N i)) := by
  ext x
  simp only [mem_translatedIntegerBox, Fintype.mem_piFinset, Finset.mem_Ico]

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.translatedIntegerBox_eq_piFinset.{u_1} := @OAI.Erdos3.translatedIntegerBox_eq_piFinset.{u_1}
