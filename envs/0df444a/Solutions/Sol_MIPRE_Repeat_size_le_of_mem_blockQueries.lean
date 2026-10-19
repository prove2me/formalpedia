-- Prove2me | solution 1 for MIPRE.Repeat.size_le_of_mem_blockQueries
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:47.716432+00:00
-- url     : https://prove2.me/submissions/2275b26c-0116-4496-af3d-96c71c530e44

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/SamplerCost.lean (solution of MIPRE.Repeat.size_le_of_mem_blockQueries);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
open Data
theorem size_list_take_le (s : ℕ) (l : List Data) : (list (l.take s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp only [List.take_zero, list_nil, size_nil, size_list_cons]; omega
    | succ s => simp only [List.take_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem size_list_drop_le (s : ℕ) (l : List Data) : (list (l.drop s)).size ≤ (list l).size := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => exact le_rfl
    | succ s => simp only [List.drop_succ_cons, size_list_cons]; have := ih s; omega
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_nil (s : ℕ) (hs : 0 < s) (y : List Data) : chunkPairs s hs [] y = [] := by
  rw [chunkPairs]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
theorem chunkPairs_cons (s : ℕ) (hs : 0 < s) (h : Data) (l y : List Data) :
    chunkPairs s hs (h :: l) y =
      ((h :: l).take s, y.take s) :: chunkPairs s hs ((h :: l).drop s) (y.drop s) := by
  rw [chunkPairs]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
section
open Data
/-- Every piece is a piece of the list it came from: the sizes are bounded. -/
theorem size_le_of_mem_chunkPairs (s : ℕ) (hs : 0 < s) (l y : List Data) :
    ∀ p ∈ chunkPairs s hs l y, (list p.1).size ≤ (list l).size ∧ (list p.2).size ≤ (list y).size := by
  induction l, y using chunkPairs.induct s hs with
  | case1 y => simp [chunkPairs_nil]
  | case2 h l y ih =>
    intro p hp
    rw [chunkPairs_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨size_list_take_le _ _, size_list_take_le _ _⟩
    · obtain ⟨h1, h2⟩ := ih p hp
      exact ⟨h1.trans (size_list_drop_le _ _), h2.trans (size_list_drop_le _ _)⟩
end
end MIPRE.Cost.Data

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
theorem _root_.solution (s : ℕ) (d q : Data) (hq : q ∈ blockQueries s d) :
    q.size ≤ d.size := by
  unfold blockQueries at hq
  split at hq
  · rename_i k₀ k₁ wD jD uD yD
    split at hq
    · rename_i hs
      rw [List.mem_map] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      obtain ⟨h1, h2⟩ := size_le_of_mem_chunkPairs s hs (toList uD) (toList yD) p hp
      rw [list_toList] at h1 h2
      simp only [size_cons]
      omega
    · simp at hq
  · simp at hq
end MIPRE.Repeat
