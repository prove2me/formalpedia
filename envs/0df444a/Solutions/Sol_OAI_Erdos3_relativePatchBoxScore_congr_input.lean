-- Prove2me | solution 1 for OAI.Erdos3.relativePatchBoxScore_congr_input
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:32:21.60105+00:00
-- url     : https://prove2.me/submissions/604b7244-9e59-44f4-a887-554855da4f54

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchBoxScore_congr_input {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) {f g : (X → ℤ) → ℝ}
    (hfg : ∀ x ∈ integerBox N, f x = g x) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A = relativePatchBoxScore N g target A := by
  apply Finset.expect_congr rfl
  intro x hx
  rw [hfg x hx]

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.relativePatchBoxScore_congr_input.{u_1} := @OAI.Erdos3.relativePatchBoxScore_congr_input.{u_1}
