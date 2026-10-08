-- Prove2me | solution 1 for OAI.Erdos3.relativeBoxInput_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:32:26.758979+00:00
-- url     : https://prove2.me/submissions/d6f29bb8-16cd-4d17-920f-9e101f90d23a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B009

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  by_cases hx : x ∈ integerBox N
  · simpa only [relativeBoxInput_eq N f hx] using hf x hx
  · simp only [relativeBoxInput, if_neg hx, Set.mem_Icc]
    constructor <;> norm_num

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.relativeBoxInput_unitInterval.{u_1} := @OAI.Erdos3.relativeBoxInput_unitInterval.{u_1}
