-- Prove2me | solution 1 for OAI.Erdos3.physicalBoxResidual_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:23:20.403414+00:00
-- url     : https://prove2.me/submissions/5fbd4c91-4586-4159-9f24-d99e635e5e0c

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

theorem physicalBoxResidual_zero_off (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (x : I → ℤ) (hx : x ∉ translatedIntegerBox lo N) :
    physicalBoxResidual lo N P hpos q b f x = 0 := by
  simp only [physicalBoxResidual, if_neg hx]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalBoxResidual_zero_off.{u_1, u_2} := @OAI.Erdos3.physicalBoxResidual_zero_off.{u_1, u_2}
