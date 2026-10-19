-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.evalCand_candOf5
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:49:59.865075+00:00
-- url     : https://prove2.me/submissions/eb76dd8a-dc8e-4ba0-ba4d-d10c1d61899e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Decoupled.lean (solution of MIPRE.TM.CookLevin.Desc.evalCand_candOf5);
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
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_evalFields_litFields
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_getD_rho
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD

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
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem clauseInput_eq (m : ℕ) (c' : Clause3 (Fin (2 ^ m))) :
    clauseInput m c' = bitsOfNat m c'.l₁.var ++ (bitsOfNat m c'.l₂.var ++
      (bitsOfNat m c'.l₃.var ++ [c'.l₁.pos, c'.l₂.pos, c'.l₃.pos])) := by
  rw [clauseInput, List.append_assoc, List.append_assoc]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
/-- The bits of the three blocks of the input of a clause. -/
theorem ibOf_clauseInput_zero :
    ibOf 0 (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₁.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega), List.drop_zero, clauseInput_eq,
    List.take_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem ibOf_clauseInput_one :
    ibOf (mOf e Gc) (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₂.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega), clauseInput_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem ibOf_clauseInput_two :
    ibOf (2 * mOf e Gc) (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      bitsOfNat (mOf e Gc) c.l₃.var := by
  rw [ibOf_getD _ _ _ (by rw [length_clauseInput]; omega)]
  have h2 : 2 * mOf e Gc = mOf e Gc + mOf e Gc := by omega
  rw [h2, ← List.drop_drop, clauseInput_eq, List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat])]
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
/-- A slice of the five-block input at a shifted base is the 3SAT describer's own slice. -/
theorem ibOf_shift {ℓ m b : ℕ}
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ m)) (Fin (2 ^ m)) (Fin (2 ^ m)))
    (h : b + m ≤ 3 * m) :
    ibOf (2 * ℓ + b) m (fun i => (clauseInput5 ℓ m c).getD i false) =
      ibOf b m (fun i => (clauseInput m (lastThree c)).getD i false) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < m := by simpa using h1
  have hr := getD_rho c (k := b + i) (by omega)
  rw [rho, if_pos (by omega)] at hr
  simp only [ibOf, List.getElem_map, List.getElem_range']
  rw [show 2 * ℓ + b + 1 * i = b + i + 2 * ℓ from by omega, hr]
  congr 1
  omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
theorem _root_.solution (ℓ e T : ℕ)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ mOf e Gc)) (Fin (2 ^ mOf e Gc))
      (Fin (2 ^ mOf e Gc))) (hT : T ≤ Sof e) :
    evalCand (candOf5 ℓ e T) (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
      candOfClause e T (lastThree c) := by
  have hlf : ∀ b, b + mOf e Gc ≤ 3 * mOf e Gc →
      evalFields (litFields e Gc T (2 * ℓ + b))
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        fieldsOf e Gc T (bitsOfNat (mOf e Gc) (lastThree c).l₁.var) ∨ True := fun _ _ => Or.inr trivial
  clear hlf
  have key : ∀ b, b + mOf e Gc ≤ 3 * mOf e Gc →
      evalFields (litFields e Gc T (2 * ℓ + b))
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        fieldsOf e Gc T (ibOf b (mOf e Gc)
          (fun i => (clauseInput (mOf e Gc) (lastThree c)).getD i false)) := by
    intro b hb
    rw [evalFields_litFields e Gc T (2 * ℓ + b) _ hT, ibOf_shift c hb]
  have hs : ∀ t : ℕ, t < 3 →
      (Fml.inp (2 * ℓ + 3 * mOf e Gc + (t + 2))).eval
          (fun i => (clauseInput5 ℓ (mOf e Gc) c).getD i false) =
        (sgList c).getD (t + 2) false := by
    intro t _
    have := eval_sgF c (t + 2)
    rwa [show sgOff ℓ (mOf e Gc) + (t + 2) = 2 * ℓ + 3 * mOf e Gc + (t + 2) from by
      unfold sgOff; omega] at this
  have h0 := key 0 (by omega)
  have h1 := key (mOf e Gc) (by omega)
  have h2 := key (2 * mOf e Gc) (by omega)
  have g0 := hs 0 (by omega)
  have g1 := hs 1 (by omega)
  have g2 := hs 2 (by omega)
  simp only [evalCand, candOf5, candOfClause, lastThree]
  rw [show 2 * ℓ + 0 = 2 * ℓ from by omega] at h0
  rw [show 2 * ℓ + 3 * mOf e Gc + 2 = 2 * ℓ + 3 * mOf e Gc + (0 + 2) from by omega]
  rw [show 2 * ℓ + 3 * mOf e Gc + 3 = 2 * ℓ + 3 * mOf e Gc + (1 + 2) from by omega]
  rw [show 2 * ℓ + 3 * mOf e Gc + 4 = 2 * ℓ + 3 * mOf e Gc + (2 + 2) from by omega]
  rw [h0, h1, h2, g0, g1, g2, ibOf_clauseInput_zero, ibOf_clauseInput_one,
    ibOf_clauseInput_two]
  rfl
end MIPRE.TM.CookLevin.Desc
