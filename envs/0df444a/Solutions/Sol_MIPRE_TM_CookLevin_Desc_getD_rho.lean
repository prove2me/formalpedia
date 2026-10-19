-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.getD_rho
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:41.033404+00:00
-- url     : https://prove2.me/submissions/355dfb0d-16f7-4a6a-ad27-7e6c468d66c5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Decoupled.lean (solution of MIPRE.TM.CookLevin.Desc.getD_rho);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem getD_drop_eq (l : BitStr) (k i : ℕ) : (l.drop k).getD i false = l.getD (k + i) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem clauseInput5_eq : clauseInput5 ℓ r c =
    bitsOfNat ℓ c.l₁.var ++ (bitsOfNat ℓ c.l₂.var ++ (bitsOfNat r c.l₃.var ++
      (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c)))) := by
  simp only [clauseInput5, sgList, List.append_assoc]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem drop_two : (clauseInput5 ℓ r c).drop (2 * ℓ) =
    bitsOfNat r c.l₃.var ++ (bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c)) := by
  have h : 2 * ℓ = ℓ + ℓ := by omega
  rw [h, ← List.drop_drop, clauseInput5_eq, List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem drop_three : (clauseInput5 ℓ r c).drop (2 * ℓ + r) =
    bitsOfNat r c.l₄.var ++ (bitsOfNat r c.l₅.var ++ sgList c) := by
  rw [← List.drop_drop, drop_two, List.drop_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem drop_four : (clauseInput5 ℓ r c).drop (2 * ℓ + 2 * r) =
    bitsOfNat r c.l₅.var ++ sgList c := by
  have h : 2 * ℓ + 2 * r = 2 * ℓ + r + r := by omega
  rw [h, ← List.drop_drop, drop_three, List.drop_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem drop_signs : (clauseInput5 ℓ r c).drop (sgOff ℓ r) = sgList c := by
  have h : sgOff ℓ r = 2 * ℓ + 2 * r + r := by unfold sgOff; omega
  rw [h, ← List.drop_drop, drop_four, List.drop_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem eval_sgF (k : ℕ) :
    (Fml.inp (sgOff ℓ r + k)).eval (fun i => (clauseInput5 ℓ r c).getD i false) =
      (sgList c).getD k false := by
  show (clauseInput5 ℓ r c).getD (sgOff ℓ r + k) false = _
  rw [← getD_drop_eq, drop_signs]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem getD_append_left {α : Type*} (pre u : List α) (d : α) {k : ℕ} (h : k < pre.length) :
    (pre ++ u).getD k d = pre.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem getD_append_right {α : Type*} (pre u : List α) (d : α) (t : ℕ) :
    (pre ++ u).getD (pre.length + t) d = u.getD t d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem drop_two' {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (clauseInput5 ℓ r c).drop (2 * ℓ) =
      (bitsOfNat r c.l₃.var ++ bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var) ++ sgList c := by
  rw [drop_two, List.append_assoc, List.append_assoc]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
theorem _root_.solution {ℓ r : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
    {k : ℕ} (hk : k < 3 * r + 3) :
    (clauseInput5 ℓ r c).getD (rho ℓ r k) false =
      (clauseInput r (lastThree c)).getD k false := by
  set pre : BitStr :=
    bitsOfNat r c.l₃.var ++ bitsOfNat r c.l₄.var ++ bitsOfNat r c.l₅.var with hpre
  have hlen : pre.length = 3 * r := by rw [hpre]; simp [length_bitsOfNat]; omega
  have h5 : clauseInput r (lastThree c) = pre ++ [c.l₃.pos, c.l₄.pos, c.l₅.pos] := by
    rw [clauseInput, hpre, lastThree]
  rcases lt_or_ge k (3 * r) with h | h
  · rw [rho, if_pos h, Nat.add_comm k (2 * ℓ), ← getD_drop_eq, drop_two',
      getD_append_left pre (sgList c) false (by rw [hlen]; exact h), h5,
      getD_append_left pre _ false (by rw [hlen]; exact h)]
  · obtain ⟨t, rfl⟩ : ∃ t, k = 3 * r + t := ⟨k - 3 * r, by omega⟩
    have ht : t < 3 := by omega
    have hL : (clauseInput5 ℓ r c).getD (rho ℓ r (3 * r + t)) false =
        (sgList c).getD (t + 2) false := by
      rw [rho, if_neg (by omega),
        show 3 * r + t + 2 * ℓ + 2 = sgOff ℓ r + (t + 2) from by unfold sgOff; omega]
      show (Fml.inp (sgOff ℓ r + (t + 2))).eval
        (fun i => (clauseInput5 ℓ r c).getD i false) = _
      exact eval_sgF c (t + 2)
    rw [hL, h5, show 3 * r + t = pre.length + t from by rw [hlen], getD_append_right]
    interval_cases t <;> rfl
end MIPRE.TM.CookLevin.Desc
