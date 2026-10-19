-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.eval_linkFml
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:18.183979+00:00
-- url     : https://prove2.me/submissions/a2583829-0534-4ccb-8c55-360423af7956

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Link.lean (solution of MIPRE.TM.CookLevin.Desc.eval_linkFml);
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
import Theorems.Thm_MIPRE_SAT_Fml_eval_addConstRel_iff
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem eval_xor (f g : Fml) (x : ℕ → Bool) : (xor f g).eval x = (f.eval x != g.eval x) := by
  simp only [xor, eval]; cases f.eval x <;> cases g.eval x <;> rfl
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
theorem eval_andList_eq_true (l : List Fml) (x : ℕ → Bool) :
    (andList l).eval x = true ↔ ∀ f ∈ l, f.eval x = true := by
  rw [eval_andList, List.all_eq_true]
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
theorem eval_orList_eq_true (l : List Fml) (x : ℕ → Bool) :
    (orList l).eval x = true ↔ ∃ f ∈ l, f.eval x = true := by
  rw [eval_orList, List.any_eq_true]
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
theorem eval_foldl_eqFStep : ∀ (fs gs : List Fml), fs.length = gs.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      ((fs.zip gs).foldl eqFStep init).eval x = (init.eval x && decide (bitsOf fs x = bitsOf gs x))
  | [], [], _, init, x => by simp
  | f :: fs, g :: gs, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_eqFStep fs gs h]
    simp only [eqFStep, eval, bitsOf_cons, List.cons.injEq, Bool.decide_and, eval_xnor]
    cases hg : g.eval x <;> cases hf : f.eval x <;> simp [hf, hg, Bool.and_assoc]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqFields (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = decide (bitsOf fs x = bitsOf gs x) := by
  rw [eqFields, eval_foldl_eqFStep fs gs h]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqFields_iff (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = true ↔ val fs x = val gs x := by
  rw [eval_eqFields fs gs h, decide_eq_true_iff, val, val]
  constructor
  · intro e; rw [e]
  · intro hv; exact bitsVal_injective (by simp [h]) hv
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
open SAT Cost Fml
theorem headD_eval_toNat (fs : List Fml) (x : ℕ → Bool) (hne : fs ≠ []) :
    ((fs.headD (const false)).eval x).toNat = val fs x % 2 := by
  cases fs with
  | nil => exact absurd rfl hne
  | cons f fs => rw [List.headD_cons, val_cons]; cases f.eval x <;> simp <;> omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_ltN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (ltConst fs (nbits w k)).eval x = true ↔ val fs x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hl, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_eqF {fs gs : List Fml} {w : ℕ} (hl : fs.length = w) (hg : gs.length = w) (x : ℕ → Bool) :
    (eqFields fs gs).eval x = true ↔ val fs x = val gs x :=
  eval_eqFields_iff _ _ (by rw [hl, hg]) x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_addN {fs gs : List Fml} {w k : ℕ} (hl : fs.length = w) (hg : gs.length = w)
    (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (addConstRel fs gs (nbits w k)).eval x = true ↔ val gs x = val fs x + k := by
  rw [eval_addConstRel_iff _ _ _ (by rw [hl, length_nbits]) (by rw [hl, hg]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_not_iff (f : Fml) (x : ℕ → Bool) : (not f).eval x = true ↔ ¬ f.eval x = true := by
  simp [eval]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₂ (a b : Fml) (x : ℕ → Bool) :
    (andList [a, b]).eval x = true ↔ a.eval x = true ∧ b.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₃ (a b c : Fml) (x : ℕ → Bool) :
    (andList [a, b, c]).eval x = true ↔ a.eval x = true ∧ b.eval x = true ∧ c.eval x = true := by
  simp [eval_andList_eq_true]
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
variable (ℓ r : ℕ)
theorem length_j₁F (h : ℓ ≤ r) : (j₁F ℓ r).length = r := by
  rw [j₁F, length_padTo _ _ (by rw [length_field]; exact h)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r : ℕ)
theorem length_j₂F (h : ℓ ≤ r) : (j₂F ℓ r).length = r := by
  rw [j₂F, length_padTo _ _ (by rw [length_field]; exact h)]
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
variable (ℓ r T : ℕ)
theorem eval_xor_iff (f g : Fml) (x : ℕ → Bool) :
    (xor f g).eval x = true ↔ f.eval x ≠ g.eval x := by
  rw [eval_xor]
  cases f.eval x <;> cases g.eval x <;> simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
theorem eval_headD_iff {fs : List Fml} (hne : fs ≠ []) (x : ℕ → Bool) :
    (fs.headD (const false)).eval x = true ↔ ¬ val fs x % 2 = 0 := by
  have h := headD_eval_toNat fs x hne
  cases hb : (fs.headD (const false)).eval x
  · rw [hb] at h; simp at h ⊢; omega
  · rw [hb] at h; simp at h ⊢; omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
theorem _root_.solution {ℓ r T : ℕ} (hℓr : ℓ ≤ r) (hr : 1 ≤ r) (hT : 2 * T < 2 ^ r)
    (c : Clause5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ)) (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r))) :
    (linkFml ℓ r T).eval (fun i => (clauseInput5 ℓ r c).getD i false) = true ↔ Link ℓ r T c := by
  have h1 := length_j₁F ℓ r hℓr
  have h2 := length_j₂F ℓ r hℓr
  have hne₁ : j₁F ℓ r ≠ [] := by
    intro hcon; rw [hcon, List.length_nil] at h1; omega
  have hne₂ : j₂F ℓ r ≠ [] := by
    intro hcon; rw [hcon, List.length_nil] at h2; omega
  set x : ℕ → Bool := fun i => (clauseInput5 ℓ r c).getD i false with hx
  -- the five indices and the five signs
  have e₁ : val (j₁F ℓ r) x = (c.l₁.var : ℕ) := val_j₁F c
  have e₂ : val (j₂F ℓ r) x = (c.l₂.var : ℕ) := val_j₂F c
  have e₃ : val (j₃F ℓ r) x = (c.l₃.var : ℕ) := val_j₃F c
  have e₄ : val (j₄F ℓ r) x = (c.l₄.var : ℕ) := val_j₄F c
  have e₅ : val (j₅F ℓ r) x = (c.l₅.var : ℕ) := val_j₅F c
  have g₁ : (s₁F ℓ r).eval x = c.l₁.pos := eval_sgF c 0
  have g₂ : (s₂F ℓ r).eval x = c.l₂.pos := eval_sgF c 1
  have g₃ : (s₃F ℓ r).eval x = c.l₃.pos := eval_sgF c 2
  have g₄ : (s₄F ℓ r).eval x = c.l₄.pos := eval_sgF c 3
  have g₅ : (s₅F ℓ r).eval x = c.l₅.pos := eval_sgF c 4
  -- the tests
  have lt₁ : (ltConst (j₁F ℓ r) (nbits r (2 * T))).eval x = true ↔ (c.l₁.var : ℕ) < 2 * T := by
    rw [eval_ltN h1 hT, e₁]
  have lt₂ : (ltConst (j₂F ℓ r) (nbits r (2 * T))).eval x = true ↔ (c.l₂.var : ℕ) < 2 * T := by
    rw [eval_ltN h2 hT, e₂]
  have eq₁₃ : (eqFields (j₁F ℓ r) (j₃F ℓ r)).eval x = true ↔
      (c.l₁.var : ℕ) = (c.l₃.var : ℕ) := by
    rw [eval_eqF h1 (length_j₃F ℓ r), e₁, e₃]
  have add₂₃ : (addConstRel (j₂F ℓ r) (j₃F ℓ r) (nbits r (2 * T))).eval x = true ↔
      (c.l₃.var : ℕ) = (c.l₂.var : ℕ) + 2 * T := by
    rw [eval_addN h2 (length_j₃F ℓ r) hT, e₂, e₃]
  have eq₃₄ : (eqFields (j₃F ℓ r) (j₄F ℓ r)).eval x = true ↔
      (c.l₃.var : ℕ) = (c.l₄.var : ℕ) := by
    rw [eval_eqF (length_j₃F ℓ r) (length_j₄F ℓ r), e₃, e₄]
  have eq₄₅ : (eqFields (j₄F ℓ r) (j₅F ℓ r)).eval x = true ↔
      (c.l₄.var : ℕ) = (c.l₅.var : ℕ) := by
    rw [eval_eqF (length_j₄F ℓ r) (length_j₅F ℓ r), e₄, e₅]
  have par₁ : ((j₁F ℓ r).headD (const false)).eval x = true ↔ ¬ (c.l₁.var : ℕ) % 2 = 0 := by
    rw [eval_headD_iff hne₁, e₁]
  have par₂ : ((j₂F ℓ r).headD (const false)).eval x = true ↔ ¬ (c.l₂.var : ℕ) % 2 = 0 := by
    rw [eval_headD_iff hne₂, e₂]
  rw [linkFml, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    eval_andList₃, eval_andList₂, eval_not_iff, eval_xor_iff, lt₁, lt₂, eq₁₃, add₂₃, eq₃₄, eq₄₅,
    par₁, par₂, g₁, g₂, g₃, g₄, g₅, Link]
  constructor
  · rintro (⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨a, b, d⟩
    · exact Or.inr (Or.inl ⟨a, b, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b⟩))))))
  · rintro (⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b⟩)
    · exact Or.inl ⟨a, b, d⟩
    · exact Or.inr (Or.inl ⟨a, b, d⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, by omega, d⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, by simpa using d⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b⟩))))))
end MIPRE.TM.CookLevin.Desc
