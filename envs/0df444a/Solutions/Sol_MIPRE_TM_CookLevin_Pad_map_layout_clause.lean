-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.map_layout_clause
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:11:07.746015+00:00
-- url     : https://prove2.me/submissions/7002bc6c-0826-4018-8f14-41788ef497b8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Padded.lean (solution of MIPRE.TM.CookLevin.Pad.map_layout_clause);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Definitions.Def_MIPRE_TM_CookLevin_Padded
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem _root_.solution {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (layout ℓ r m).map (fun i => (clauseInput5 m m
      (c.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
        (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr))).getD i false) =
      clauseInput5 ℓ r c := by
  let a := bitsOfNat m c.l₁.var
  let b := bitsOfNat m c.l₂.var
  let u := bitsOfNat m c.l₃.var
  let v := bitsOfNat m c.l₄.var
  let w := bitsOfNat m c.l₅.var
  let signs := [c.l₁.pos, c.l₂.pos, c.l₃.pos, c.l₄.pos, c.l₅.pos]
  let input := a ++ b ++ u ++ v ++ w ++ signs
  have lengths : a.length = m ∧ b.length = m ∧ u.length = m ∧ v.length = m ∧ w.length = m := by
    simp [a, b, u, v, w]
  have h₁ : ibOf 0 ℓ (fun i => input.getD i false) = bitsOfNat ℓ c.l₁.var := by
    simpa only [List.length_nil, List.nil_append, input, a, List.append_assoc] using
      slice_index [] (b ++ u ++ v ++ w ++ signs) m ℓ c.l₁.var hℓ
  have h₂ : ibOf m ℓ (fun i => input.getD i false) = bitsOfNat ℓ c.l₂.var := by
    simpa only [lengths.1, input, b, List.append_assoc] using
      slice_index a (u ++ v ++ w ++ signs) m ℓ c.l₂.var hℓ
  have h₃ : ibOf (2 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₃.var := by
    simpa only [List.length_append, lengths.1, lengths.2.1, two_mul, input, u, List.append_assoc] using
      slice_index (a ++ b) (v ++ w ++ signs) m r c.l₃.var hr
  have h₄ : ibOf (3 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₄.var := by
    have he : (a ++ b ++ u).length = 3 * m := by simp [a, b, u]; omega
    have hh := slice_index (a ++ b ++ u) (w ++ signs) m r c.l₄.var hr
    rw [he] at hh
    simpa only [input, v, List.append_assoc] using hh
  have h₅ : ibOf (4 * m) r (fun i => input.getD i false) = bitsOfNat r c.l₅.var := by
    have he : (a ++ b ++ u ++ v).length = 4 * m := by simp [a, b, u, v]; omega
    have hh := slice_index (a ++ b ++ u ++ v) signs m r c.l₅.var hr
    rw [he] at hh
    simpa only [input, w, List.append_assoc] using hh
  have hs : ibOf (5 * m) 5 (fun i => input.getD i false) = signs := by
    have he : (a ++ b ++ u ++ v ++ w).length = 5 * m := by simp [a, b, u, v, w]; omega
    rw [← he, ibOf_getD _ _ _ (by simp only [input, List.length_append, he]; simp [signs])]
    change ((a ++ b ++ u ++ v ++ w ++ signs).drop _).take 5 = _
    rw [List.drop_left' rfl]
    exact List.take_of_length_le (by simp [signs])
  change (layout ℓ r m).map (fun i => input.getD i false) = _
  simp only [layout, List.map_append]
  change ibOf 0 ℓ _ ++ ibOf m ℓ _ ++ ibOf (2 * m) r _ ++
    ibOf (3 * m) r _ ++ ibOf (4 * m) r _ ++ ibOf (5 * m) 5 _ = _
  rw [h₁, h₂, h₃, h₄, h₅, hs]
  rfl
end MIPRE.TM.CookLevin.Pad
