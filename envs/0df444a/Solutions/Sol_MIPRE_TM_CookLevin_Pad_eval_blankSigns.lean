-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.eval_blankSigns
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:11:08.371764+00:00
-- url     : https://prove2.me/submissions/7611354d-74c9-4a60-89cc-43100b376a10

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Padded.lean (solution of MIPRE.TM.CookLevin.Pad.eval_blankSigns);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_xnor (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = (f.eval x == g.eval x) := by
  simp only [xnor, eval]; cases f.eval x <;> cases g.eval x <;> rfl
end
end MIPRE.SAT.Fml

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m)
    (c : Clause5 (Fin (2 ^ m)) (Fin (2 ^ m))
      (Fin (2 ^ m)) (Fin (2 ^ m)) (Fin (2 ^ m))) :
    ((blankSign 0 (5 * m)).eval (fun i => (clauseInput5 m m c).getD i false) = true ↔
      c.l₁.pos = decide ((c.l₁.var : ℕ) % 2 = 0)) ∧
    ((blankSign m (5 * m + 1)).eval (fun i => (clauseInput5 m m c).getD i false) = true ↔
      c.l₂.pos = decide ((c.l₂.var : ℕ) % 2 = 0)) := by
  have hs0 := eval_sgF c 0
  have hs1 := eval_sgF c 1
  have hoff : sgOff m m = 5 * m := by unfold sgOff; omega
  simp only [hoff, Nat.add_zero, sgList, List.getD_cons_zero, List.getD_cons_succ] at hs0 hs1
  simp only [Fml.eval] at hs0 hs1
  have h0 : (clauseInput5 m m c).getD 0 false = (c.l₁.var : ℕ).testBit 0 := by
    rw [clauseInput5_eq, getD_append_left _ _ false (by simp; omega), getD_bitsOfNat _ (by omega)]
  have h1 : (clauseInput5 m m c).getD m false = (c.l₂.var : ℕ).testBit 0 := by
    change (clauseInput5 m m c).getD (m + 0) false = _
    rw [← getD_drop_eq, clauseInput5_eq,
      List.drop_left' (by simp), getD_append_left _ _ false (by simp; omega),
      getD_bitsOfNat _ (by omega)]
  have hp (j : ℕ) : (!(j.testBit 0)) = decide (j % 2 = 0) := by
    rw [Nat.testBit_zero]
    by_cases h : j % 2 = 0 <;> simp [h, show (j % 2 = 1) ↔ ¬ j % 2 = 0 by omega]
  simp only [blankSign, eval_xnor, beq_iff_eq, hs0, hs1, Fml.eval, h0, h1, hp]
  exact ⟨trivial, trivial⟩
end MIPRE.TM.CookLevin.Pad
