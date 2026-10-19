-- Prove2me | solution 1 for MIPRE.Repeat.loop_calls_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:50:49.871837+00:00
-- url     : https://prove2.me/submissions/d3e9f535-463e-40c8-a5db-140480acf591

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (solution of MIPRE.Repeat.loop_calls_time);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
import Theorems.Thm_MIPRE_Repeat_mem_decQueries

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
theorem _root_.solution (D : Decider) (n : ℕ) (R : Budget) (hD : D.TimeBoundAt n R.D R.k)
    (s k : ℕ) (remX remY remA remB : List Data) :
    ∃ fq : Data → Data, ∀ q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB,
      ∃ t ≤ selfUniversal.bound.eval (esize D.prog +
        (esize n + ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3)
          + 1) +
        R.D * ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 + 1)
          ^ R.k),
        Eval [q] selfUniversal.univ (fq q) t := by
  classical
  have key : ∀ q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB,
      ∃ r t, t ≤ selfUniversal.bound.eval (esize D.prog +
        (esize n + ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3)
          + 1) +
        R.D * ((list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 + 1)
          ^ R.k) ∧ Eval [q] selfUniversal.univ r t := by
    intro q hq
    obtain ⟨xi, yi, ai, bi, rfl, h1, h2, h3, h4⟩ := mem_decQueries k remX remY remA remB q hq
    obtain ⟨r, t, ht, run⟩ := hD (.cons xi (.cons yi (.cons ai bi)))
    obtain ⟨t', ht', run'⟩ := selfUniversal.time_le _ _ _ _ run
    refine ⟨r, t', ht'.trans (polynomial_eval_mono _ ?_), run'⟩
    have hsz : (Data.cons xi (.cons yi (.cons ai bi))).size ≤
        (list remX).size + (list remY).size + (list remA).size + (list remB).size + 3 := by
      simp only [size_cons]; omega
    have hk := Nat.mul_le_mul_left R.D (Nat.pow_le_pow_left (Nat.add_le_add_right hsz 1) R.k)
    have he : (encode n : Data).size = esize n := rfl
    simp only [size_cons, he] at ht ⊢
    simp only [size_cons] at hsz hk
    omega
  refine ⟨fun q => if h : q ∈ decQueries (encode D.prog) (encode n) s k remX remY remA remB then
    (key q h).choose else .nil, fun q hq => ?_⟩
  simp only [dif_pos hq]
  obtain ⟨t, ht, run⟩ := (key q hq).choose_spec
  exact ⟨t, ht, run⟩
end MIPRE.Repeat
