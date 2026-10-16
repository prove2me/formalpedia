-- Prove2me | solution 1 for MIPRE.Verifier.hasPerfectPCC_of_accepts_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:02:08.359944+00:00
-- url     : https://prove2.me/submissions/55ab3cb0-13b7-4646-9082-945318dd6459

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Classes.lean (solution of MIPRE.Verifier.hasPerfectPCC_of_accepts_diagonal);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
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
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Theorems.Thm_MIPRE_SyncStrategy_value_const

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
/-- The constant strategy is PCC. -/
theorem isPCC_const (G : SynchronousGame X A) (a₀ : A) : (const G a₀).IsPCC := by
  intro x y _ a b
  show (if a = a₀ then (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) else 0) *
      (if b = a₀ then 1 else 0) = (if b = a₀ then 1 else 0) * (if a = a₀ then 1 else 0)
  split_ifs <;> first | exact Commute.one_left _ | exact Commute.zero_left _
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem _root_.solution {n T : ℕ} (a₀ : Answers T)
    (hacc : ∀ x y : V.Questions n, V.decider.Accepts n (CL.toBits x) (CL.toBits y) a₀.1 a₀.1) :
    V.HasPerfectPCC n T := by
  classical
  refine ⟨SyncStrategy.const (V.doubledGame n T) a₀, SyncStrategy.isPCC_const _ _, ?_⟩
  rw [SyncStrategy.value_const]
  have hD : ∀ x y : V.Questions n, ((V.game n T).D x y a₀ a₀ = true) := fun x y =>
    decide_eq_true (hacc x y)
  calc ∑ p, ∑ q, (V.doubledGame n T).μ p q *
        (if (V.doubledGame n T).D p q a₀ a₀ then (1 : ℝ) else 0)
      = ∑ p, ∑ q, (V.doubledGame n T).μ p q := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        by_cases h : p.1 = false ∧ q.1 = true
        · simp [doubledGame, h, hD]
        · simp [doubledGame, h]
    _ = 1 := (V.doubledGame n T).μ_sum_one
end MIPRE.Verifier
