-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.formula5_circuit
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:13:42.916616+00:00
-- url     : https://prove2.me/submissions/e510aa5d-9ff5-43fb-9d02-30c3df3dde6e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Padded.lean (solution of MIPRE.TM.CookLevin.Pad.formula5_circuit);
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
import Theorems.Thm_MIPRE_SAT_Fml_eval_toCircuit
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_eval_blankSigns
import Theorems.Thm_MIPRE_TM_CookLevin_Pad_map_layout_clause

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem evalBits_toCircuit (n : ℕ) (f : Fml) (l : List Bool) :
    (f.toCircuit n).evalBits l = f.eval fun i => l.getD i false :=
  eval_toCircuit n f _
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_append (l₁ l₂ : BitStr) :
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂ := by
  induction l₁ with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    rw [List.cons_append, bitsVal_cons', bitsVal_cons', ih, List.length_cons, Nat.pow_succ]; ring
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_replicate_false (n : ℕ) : bitsVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, bitsVal_cons', ih]; rfl
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_padBits (W : ℕ) (l : BitStr) : bitsVal (padBits W l) = bitsVal l := by
  rw [padBits, bitsVal_append, bitsVal_replicate_false]; ring
end
end MIPRE.SAT

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_xnor (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = (f.eval x == g.eval x) := by
  simp only [xnor, eval]; cases f.eval x <;> cases g.eval x <;> rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_foldl_and (l : List Fml) (init : Fml) (x : ℕ → Bool) :
    (l.foldl and init).eval x = (init.eval x && l.all (·.eval x)) := by
  induction l generalizing init with
  | nil => simp
  | cons f l ih => simp [List.foldl_cons, ih, eval, Bool.and_assoc]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_andList (l : List Fml) (x : ℕ → Bool) : (andList l).eval x = l.all (·.eval x) := by
  rw [andList, eval_foldl_and]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_foldl_or (l : List Fml) (init : Fml) (x : ℕ → Bool) :
    (l.foldl or init).eval x = (init.eval x || l.any (·.eval x)) := by
  induction l generalizing init with
  | nil => simp
  | cons f l ih => simp [List.foldl_cons, ih, eval, Bool.or_assoc]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_orList (l : List Fml) (x : ℕ → Bool) : (orList l).eval x = l.any (·.eval x) := by
  rw [orList, eval_foldl_or]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    val (f :: fs) x = 2 * val fs x + (f.eval x).toNat := by
  simp only [val, bitsOf_cons]; rw [bitsVal_cons']
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem bitsOf_field (a W : ℕ) (x : ℕ → Bool) : bitsOf (field a W) x = (List.range' a W).map x := by
  simp [bitsOf, field, List.map_map, Function.comp_def, eval]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_padTo (W : ℕ) (fs : List Fml) (h : fs.length ≤ W) : (padTo W fs).length = W := by
  simp [padTo]; omega
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem bitsOf_padTo (W : ℕ) (fs : List Fml) (x : ℕ → Bool) :
    bitsOf (padTo W fs) x = padBits W (bitsOf fs x) := by
  simp [bitsOf, padTo, padBits, List.map_append, List.map_replicate, eval]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_padTo (W : ℕ) (fs : List Fml) (x : ℕ → Bool) : val (padTo W fs) x = val fs x := by
  rw [val, bitsOf_padTo, bitsVal_padBits]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_foldl_ltStep : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      (((fs.zip c).foldl ltStep init).eval x = true ↔
        val fs x < bitsVal c ∨ (val fs x = bitsVal c ∧ init.eval x = true))
  | [], [], _, init, x => by simp [val, bitsVal_nil]
  | f :: fs, b :: c, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_ltStep fs c h, val_cons, bitsVal_cons']
    simp only [ltStep, eval, eval_xnor, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq]
    cases b <;> cases hf : f.eval x <;> simp <;> omega
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_ltConst_iff (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (ltConst fs c).eval x = true ↔ val fs x < bitsVal c := by
  rw [ltConst, eval_foldl_ltStep fs c h]; simp [eval]
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem bitsVal_nbits (w n : ℕ) : bitsVal (nbits w n) = n % 2 ^ w := bitsVal_bitsOfNat w n
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem bitsVal_nbits_of_lt {w n : ℕ} (h : n < 2 ^ w) : bitsVal (nbits w n) = n := by
  rw [bitsVal_nbits, Nat.mod_eq_of_lt h]
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
theorem val_j₁F :
    val (j₁F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) = (c.l₁.var : ℕ) := by
  rw [j₁F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf 0 ℓ _) = _
  rw [ibOf_getD _ 0 ℓ (by rw [length_clauseInput5]; omega), List.drop_zero, clauseInput5_eq,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₁.var.isLt]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem val_j₂F :
    val (j₂F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) = (c.l₂.var : ℕ) := by
  rw [j₂F, val_padTo, val, bitsOf_field]
  show bitsVal (ibOf ℓ ℓ _) = _
  rw [ibOf_getD _ ℓ ℓ (by rw [length_clauseInput5]; omega), clauseInput5_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.take_left' (by rw [length_bitsOfNat]),
    bitsVal_bitsOfNat, Nat.mod_eq_of_lt c.l₂.var.isLt]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem val_j₃F : val (j₃F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₃.var : ℕ) := by
  rw [j₃F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ) r _) = _
  rw [ibOf_getD _ (2 * ℓ) r (by rw [length_clauseInput5]; omega), drop_two,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₃.var.isLt]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem val_j₄F : val (j₄F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₄.var : ℕ) := by
  rw [j₄F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ + r) r _) = _
  rw [ibOf_getD _ (2 * ℓ + r) r (by rw [length_clauseInput5]; omega), drop_three,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₄.var.isLt]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
variable {ℓ r : ℕ}
  (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
theorem val_j₅F : val (j₅F ℓ r) (fun i => (clauseInput5 ℓ r c).getD i false) =
    (c.l₅.var : ℕ) := by
  rw [j₅F, val, bitsOf_field]
  show bitsVal (ibOf (2 * ℓ + 2 * r) r _) = _
  rw [ibOf_getD _ (2 * ℓ + 2 * r) r (by rw [length_clauseInput5]; omega), drop_four,
    List.take_left' (by rw [length_bitsOfNat]), bitsVal_bitsOfNat,
    Nat.mod_eq_of_lt c.l₅.var.isLt]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.SAT.Fml
section
open Cost Cost.PolyTimeFun
/-- Only the input positions used by a bounded formula affect its value. -/
theorem eval_congr_of_inputsLt {n : ℕ} {f : Fml} (hf : f.InputsLt n)
    (x y : ℕ → Bool) (hxy : ∀ i < n, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | inp i => exact hxy i hf
  | const b => rfl
  | and f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]
  | or f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]
  | not f ih => simp only [eval, ih hf]
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem eval_low (base old m : ℕ) (hm : old ≤ m) (x : ℕ → Bool) :
    (low base old m).eval x = true ↔ val (field base m) x < 2 ^ old := by
  unfold low
  rw [eval_ltConst_iff _ _ (by simp [length_padTo]), val_padTo,
    bitsVal_nbits_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
end
end MIPRE.TM.CookLevin.Pad

namespace MIPRE.TM.CookLevin.Pad
section
open SAT Cost Cost.PolyTimeFun Fml Desc
/-- On an embedded clause, the renamed old formula has exactly its old value. -/
theorem eval_renamed_clause {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5))
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (Fml.rename (fun i => (layout ℓ r m).getD i 0) f).eval
      (fun i => (clauseInput5 m m
        (c.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
          (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr))).getD i false) =
      f.eval (fun i => (clauseInput5 ℓ r c).getD i false) := by
  rw [Fml.eval_rename]
  apply Fml.eval_congr_of_inputsLt hf
  intro i hi
  have hlen : i < (layout ℓ r m).length := by simpa using hi
  have hh := congrArg (fun l : BitStr => l.getD i false) (map_layout_clause hℓ hr c)
  rw [List.getD_eq_getElem _ false (by simpa using hlen), List.getElem_map] at hh
  simpa only [Function.comp_apply, List.getD_eq_getElem _ 0 hlen] using hh
end
end MIPRE.TM.CookLevin.Pad

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem _root_.solution {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m) (hm : 1 ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (circuit ℓ r m f).formula5 m m =
      Cnf5.pad hℓ hr ((f.toCircuit (2 * ℓ + 3 * r + 5)).formula5 ℓ r) := by
  ext c
  let x := fun i => (clauseInput5 m m c).getD i false
  have h₁ : (low 0 ℓ m).eval x = true ↔ (c.l₁.var : ℕ) < 2 ^ ℓ := by
    rw [eval_low _ _ _ hℓ]
    have hv := val_j₁F c
    simpa only [j₁F, val_padTo] using iff_of_eq (congrArg (fun t => t < 2 ^ ℓ) hv)
  have h₂ : (low m ℓ m).eval x = true ↔ (c.l₂.var : ℕ) < 2 ^ ℓ := by
    rw [eval_low _ _ _ hℓ]
    have hv := val_j₂F c
    simpa only [j₂F, val_padTo] using iff_of_eq (congrArg (fun t => t < 2 ^ ℓ) hv)
  have h₃ : (low (2 * m) r m).eval x = true ↔ (c.l₃.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    exact iff_of_eq (congrArg (fun t => t < 2 ^ r) (val_j₃F c))
  have h₄ : (low (3 * m) r m).eval x = true ↔ (c.l₄.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    have hv := val_j₄F c
    have hoff : 2 * m + m = 3 * m := by omega
    simpa only [j₄F, hoff] using iff_of_eq (congrArg (fun t => t < 2 ^ r) hv)
  have h₅ : (low (4 * m) r m).eval x = true ↔ (c.l₅.var : ℕ) < 2 ^ r := by
    rw [eval_low _ _ _ hr]
    have hv := val_j₅F c
    have hoff : 2 * m + 2 * m = 4 * m := by omega
    simpa only [j₅F, hoff] using iff_of_eq (congrArg (fun t => t < 2 ^ r) hv)
  obtain ⟨hb₁, hb₂⟩ := eval_blankSigns hm c
  change ((blankSign 0 (5 * m)).eval x = true ↔ _) at hb₁
  change ((blankSign m (5 * m + 1)).eval x = true ↔ _) at hb₂
  change (circuit ℓ r m f).evalBits (clauseInput5 m m c) = true ↔ _
  rw [circuit, Fml.evalBits_toCircuit]
  change (formula ℓ r m f).eval x = true ↔ _
  simp only [formula, eval_orList, List.any_cons, List.any_nil, Fml.eval,
    eval_andList, List.all_cons, List.all_nil, Bool.and_true, Bool.or_false,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', h₁, h₂, h₃, h₄, h₅, hb₁, hb₂]
  constructor
  · rintro (⟨⟨hi₁, hi₂, hi₃, hi₄, hi₅⟩, hval⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · let c₀ : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
          (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)) :=
        ⟨⟨⟨c.l₁.var, hi₁⟩, c.l₁.pos⟩, ⟨⟨c.l₂.var, hi₂⟩, c.l₂.pos⟩,
          ⟨⟨c.l₃.var, hi₃⟩, c.l₃.pos⟩, ⟨⟨c.l₄.var, hi₄⟩, c.l₄.pos⟩,
          ⟨⟨c.l₅.var, hi₅⟩, c.l₅.pos⟩⟩
      have hmap : c₀.map (Cnf5.blockInclusion hℓ) (Cnf5.blockInclusion hℓ)
          (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) (Cnf5.blockInclusion hr) = c := rfl
      refine Or.inl ⟨c₀, ?_, hmap⟩
      change (f.toCircuit _).evalBits (clauseInput5 ℓ r c₀) = true
      rw [Fml.evalBits_toCircuit]
      have he := eval_renamed_clause hℓ hr f hf c₀
      rw [hmap] at he
      exact he.symm.trans hval
    · exact Or.inr (Or.inl ⟨Nat.not_lt.mp (fun h => by rw [h₁.mpr h] at hi; contradiction), ho⟩)
    · exact Or.inr (Or.inr ⟨Nat.not_lt.mp (fun h => by rw [h₂.mpr h] at hi; contradiction), ho⟩)
  · rintro (⟨c₀, hc₀, rfl⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · refine Or.inl ⟨⟨c₀.l₁.var.isLt, c₀.l₂.var.isLt, c₀.l₃.var.isLt,
        c₀.l₄.var.isLt, c₀.l₅.var.isLt⟩, ?_⟩
      have he := eval_renamed_clause hℓ hr f hf c₀
      exact he.trans (by simpa only [Circuit.formula5, Set.mem_ofPred_eq,
        Fml.evalBits_toCircuit] using hc₀)
    · refine Or.inr (Or.inl ⟨?_, ho⟩)
      exact Bool.eq_false_iff.mpr (fun h => Nat.not_lt.mpr hi (h₁.mp h))
    · refine Or.inr (Or.inr ⟨?_, ho⟩)
      exact Bool.eq_false_iff.mpr (fun h => Nat.not_lt.mpr hi (h₂.mp h))
end MIPRE.TM.CookLevin.Pad
