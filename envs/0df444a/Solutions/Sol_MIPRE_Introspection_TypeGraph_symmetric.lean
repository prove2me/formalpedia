-- Prove2me | solution 1 for MIPRE.Introspection.TypeGraph.symmetric
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:24.024218+00:00
-- url     : https://prove2.me/submissions/fe9188c4-0ee4-49d8-ad09-090448ef8c05

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypeGraph.lean (solution of MIPRE.Introspection.TypeGraph.symmetric);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.TypeGraph
section
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
theorem adj_symm (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (t u : QuestionType PauliType ℓ) : adj E X Z t u = adj E X Z u t := by
  simp only [adj, eq_comm]
  ac_rfl
end
end MIPRE.Introspection.TypeGraph

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypeGraph
open QuestionType Finset
set_option linter.unusedSectionVars false
variable {PauliType : Type*} [DecidableEq PauliType] {ℓ : ℕ}
theorem _root_.solution (E : PauliType → PauliType → Bool) (X Z : PauliType) :
    ∀ t u : QuestionType PauliType ℓ, Adj E X Z t u → Adj E X Z u t := by
  intro t u h
  change adj E X Z u t = true
  rw [adj_symm]
  exact h
end MIPRE.Introspection.TypeGraph
