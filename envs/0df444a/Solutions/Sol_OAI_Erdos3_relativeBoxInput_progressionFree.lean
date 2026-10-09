-- Prove2me | solution 1 for OAI.Erdos3.relativeBoxInput_progressionFree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:09:19.623685+00:00
-- url     : https://prove2.me/submissions/e10a4ae1-33eb-4185-b59d-795cae37c2d9

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B099

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_progressionFree {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree {x | x ∈ integerBox N ∧ relativeBoxInput N f x ≠ 0} k := by
  convert hfree using 1
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.relativeBoxInput_progressionFree.{u_1} := @OAI.Erdos3.relativeBoxInput_progressionFree.{u_1}
