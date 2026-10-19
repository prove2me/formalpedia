-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.nbitsR_apply
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:26.507853+00:00
-- url     : https://prove2.me/submissions/05e9ace8-e2b8-4a54-ac4f-d07cfc29e8a3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/LayoutProg.lean (solution of MIPRE.TM.CookLevin.Desc.nbitsR_apply);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem getD_bitsOfNat {w : ℕ} (n : ℕ) {i : ℕ} (hi : i < w) :
    (bitsOfNat w n).getD i false = n.testBit i := by
  rw [bitsOfNat, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem length_resize (w : ℕ) (bs : BitStr) : (resize w bs).length = w := by
  rw [resize, List.length_take, List.length_append, List.length_replicate]
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_append_replicate (bs : BitStr) (w i : ℕ) :
    (bs ++ List.replicate w false).getD i false = bs.getD i false := by
  rcases lt_or_ge i bs.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h,
      List.getElem?_eq_none h]
    rcases lt_or_ge (i - bs.length) w with h' | h'
    · rw [List.getElem?_replicate_of_lt h']; rfl
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact h')]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem getD_resize {w : ℕ} (bs : BitStr) {i : ℕ} (hi : i < w) :
    (resize w bs).getD i false = bs.getD i false := by
  rw [resize, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    ← List.getD_eq_getElem?_getD, getD_append_replicate]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
/-- **A constant of a width is a resize**: if the bits of `bs` are those of `k`, then the low
`w` bits of `bs` are the `w`-bit constant `k`. -/
theorem resize_eq_nbits (w : ℕ) (bs : BitStr) (k : ℕ)
    (h : ∀ i, bs.getD i false = k.testBit i) : resize w bs = nbits w k := by
  refine List.ext_getElem (by rw [length_resize, length_nbits]) fun i h1 h2 => ?_
  have hi : i < w := by rw [length_resize] at h1; exact h1
  rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2, getD_resize bs hi,
    h i, nbits, getD_bitsOfNat k hi]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Cost.PolyTimeFun
variable {ι : Type*} [SizedEncoding ι]
theorem _root_.solution {w : PolyTimeFun ι Unary} {bs : PolyTimeFun ι BitStr} {i : ι} (k : ℕ)
    (h : ∀ j, (bs i).getD j false = k.testBit j) : nbitsR w bs i = nbits (w i).length k :=
  resize_eq_nbits _ _ _ h
end MIPRE.TM.CookLevin.Desc
