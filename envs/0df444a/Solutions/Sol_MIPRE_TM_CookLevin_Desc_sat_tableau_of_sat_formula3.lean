-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:30:06.566966+00:00
-- url     : https://prove2.me/submissions/81347382-2ab7-4826-9e86-2c8af0bded48

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Sat.lean (solution of MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3);
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
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Theorems.Thm_MIPRE_SAT_Fml_eval_addConstRel_iff
import Theorems.Thm_MIPRE_SAT_Fml_eval_toCircuit
import Theorems.Thm_MIPRE_SAT_Fml_exists_circuit
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_cell_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_emitBad_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_emitOne_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_emitted_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_fieldsOf_idxOf
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_head_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_decodeVar_state_iff
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_evalFields_litFields
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_eval_isAuxF
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_eval_winMatchN
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_exists_cell
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_ibOf_getD
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_tapeSpec
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_windowPred_iff

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
theorem length_incBits_ge (l : BitStr) : l.length ≤ (incBits l).length := by
  induction l with
  | nil => simp [incBits]
  | cons b l ih => cases b <;> simp only [incBits, List.length_cons] <;> omega
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem length_twosComp (c : BitStr) : (twosComp c).length = c.length := by
  unfold twosComp
  rw [List.length_take]
  have := length_incBits_ge (c.map not)
  simp only [List.length_map] at this
  omega
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
theorem eval_mux (s a b : Fml) (x : ℕ → Bool) :
    (mux s a b).eval x = if s.eval x then a.eval x else b.eval x := by
  simp only [mux, eval]; cases s.eval x <;> simp
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
theorem eval_foldl_eqStep : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      ((fs.zip c).foldl eqStep init).eval x = (init.eval x && decide (bitsOf fs x = c))
  | [], [], _, init, x => by simp
  | f :: fs, b :: c, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_eqStep fs c h]
    simp only [eqStep, eval, bitsOf_cons, List.cons.injEq, Bool.decide_and]
    cases b <;> cases hf : f.eval x <;> simp [hf, eval, Bool.and_assoc]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqConst (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (eqConst fs c).eval x = decide (bitsOf fs x = c) := by
  rw [eqConst, eval_foldl_eqStep fs c h]; rfl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_eqConst_iff (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    (eqConst fs c).eval x = true ↔ val fs x = bitsVal c := by
  rw [eval_eqConst fs c h, decide_eq_true_iff, val]
  constructor
  · rintro rfl; rfl
  · intro hv; exact bitsVal_injective (by simp [h]) hv
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

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_foldl_ltFStep : ∀ (fs gs : List Fml), fs.length = gs.length →
    ∀ (init : Fml) (x : ℕ → Bool),
      (((fs.zip gs).foldl ltFStep init).eval x = true ↔
        val fs x < val gs x ∨ (val fs x = val gs x ∧ init.eval x = true))
  | [], [], _, init, x => by simp [val, bitsVal_nil]
  | f :: fs, g :: gs, h, init, x => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.foldl_cons, eval_foldl_ltFStep fs gs h, val_cons, val_cons]
    simp only [ltFStep, eval, eval_xnor, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq]
    cases hg : g.eval x <;> cases hf : f.eval x <;> simp <;> omega
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem eval_ltFields_iff (fs gs : List Fml) (h : fs.length = gs.length) (x : ℕ → Bool) :
    (ltFields fs gs).eval x = true ↔ val fs x < val gs x := by
  rw [ltFields, eval_foldl_ltFStep fs gs h]; simp [eval]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_addBits : ∀ (fs : List Fml) (c : BitStr), fs.length = c.length → ∀ cin,
    (addBits fs c cin).1.length = fs.length
  | [], [], _, _ => rfl
  | f :: fs, b :: c, h, cin => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [addBits, length_addBits fs c h]
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) :
    (addConstBits fs c).length = fs.length := length_addBits fs c h _
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem length_subConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) :
    (subConstBits fs c).length = fs.length :=
  length_addConstBits fs _ (by rw [length_twosComp]; exact h)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.refsLt {C : Circuit} (h : C.WellFormed) : C.RefsLt := h.refs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.inputsLt {C : Circuit} (h : C.WellFormed) : C.InputsLt := h.inputs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symOfCode_symCode (v : CellVal Sym) : symOfCode (symCode v) = some v := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symOfCode_eq_some {k : ℕ} {v : CellVal Sym} (h : symOfCode k = some v) : symCode v = k := by
  match k, h with
  | 0, h => cases h; rfl
  | 1, h => cases h; rfl
  | 2, h => cases h; rfl
  | 3, h => cases h; rfl
  | 4, h => cases h; rfl
  | 5, h => cases h; rfl
  | 6, h => cases h; rfl
  | n + 7, h => simp [symOfCode] at h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem tapeOfCode_eq_some {k : ℕ} {d : Tape 7 6} (h : tapeOfCode k = some d) : tapeCode d = k := by
  unfold tapeOfCode at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; simp [tapeCode]; omega
    · cases h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem qCode_lt (q : Option Ctl) : qCode q < QC := by
  unfold QC; exact (Fintype.equivFin (Option Ctl) q).isLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem qOfCode_eq_some {k : ℕ} {q : Option Ctl} (h : qOfCode k = some q) : qCode q = k := by
  unfold qOfCode at h
  split at h
  · cases h; simp [qCode]
  · cases h
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem QC_lt_two_pow_Qb : QC < 2 ^ Qb := by
  rw [Qb]
  exact Nat.lt_size_self QC
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem G_lt_two_pow_Gb (G : ℕ) : G < 2 ^ Gb G := Nat.lt_size_self G
end
end MIPRE.TM.CookLevin.Desc

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
open Interp SAT Cost
variable (e G : ℕ)
/-- `S < 2^W` and `2S + 7 < 2^W`. -/
theorem numCells_lt_two_pow_W : numCells (Sof e) < 2 ^ W e := by
  unfold numCells Sof W
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]
  have := Nat.one_le_two_pow (n := e)
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem length_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) :
    (muxList s as bs).length = as.length := by
  simp [muxList, h]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
theorem W_le_flagOff : W e + 1 ≤ flagOff e G := by unfold flagOff; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
theorem length_jF : (jF e G b).length = flagOff e G := by simp [jF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
theorem length_rF : (rF e G T b).length = flagOff e G := by
  rw [rF, length_muxList _ _ _ (by rw [length_jF, length_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]), length_jF]),
    length_jF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
theorem length_pAnsF : (pAnsF e G T b).length = W e := by
  rw [pAnsF, length_addConstBits _ _ (by simp [List.length_take, length_rF]; have := W_le_flagOff e G; omega)]
  simp [List.length_take, length_rF]; have := W_le_flagOff e G; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem length_dAns : (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6)).length = 4 := by
  rw [length_muxList _ _ _ (by simp)]; simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem length_vAns : (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5)).length = 3 := by
  rw [length_muxList _ _ _ (by simp)]; simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem litFields_lengths (e G T b : ℕ) : (litFields e G T b).Lengths e G where
  tag := by simp [litFields, length_muxList]
  t := by simp [litFields, length_muxList]
  d := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_dAns]; simp)]; simp
  p := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_pAnsF]; simp)]; simp
  v := by simp only [litFields]; rw [length_muxList _ _ _ (by rw [length_vAns]; simp)]; simp
  q := by simp [litFields, length_muxList]
  js k := by simp [litFields, length_muxList]
  g := by simp [litFields, length_muxList]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_eqTag (k : ℕ) (hk : k < 8) :
    (eqConst A.tag (nbits 3 k)).eval x = true ↔ val A.tag x = k := by
  rw [eval_eqConst_iff _ _ (by rw [hA.tag, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_ltT (k : ℕ) (hk : k < 2 ^ W e) :
    (ltConst A.t (nbits (W e) k)).eval x = true ↔ val A.t x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.t, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_ltD (k : ℕ) (hk : k < 16) :
    (ltConst A.d (nbits 4 k)).eval x = true ↔ val A.d x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.d, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_ltP (k : ℕ) (hk : k < 2 ^ W e) :
    (ltConst A.p (nbits (W e) k)).eval x = true ↔ val A.p x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.p, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_ltV (k : ℕ) (hk : k < 8) :
    (ltConst A.v (nbits 3 k)).eval x = true ↔ val A.v x < k := by
  rw [eval_ltConst_iff _ _ (by rw [hA.v, length_nbits]), bitsVal_nbits_of_lt hk]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
omit hA in
theorem S_succ_lt : Sof e + 1 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isCellF : (isCellF e A).eval x = true ↔ IsCell e (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  simp only [isCellF, IsCell, evalFields, eval, Bool.or_eq_true, eval_andList_eq_true,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true, and_true, Bool.not_eq_true',
    eval_eqTag e G hA x 0 (by omega), eval_ltT e G hA x _ hS, eval_ltD e G hA x 13 (by omega),
    eval_ltD e G hA x 7 (by omega), eval_ltP e G hA x _ hC, eval_ltV e G hA x 7 (by omega),
    eval_eqConst_iff A.t (nbits (W e) 0) (by rw [hA.t, length_nbits]), bitsVal_nbits, Nat.zero_mod,
    Nat.lt_succ_iff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isHeadF : (isHeadF e A).eval x = true ↔ IsHead e (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  simp only [isHeadF, IsHead, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 1 (by omega), eval_ltT e G hA x _ hS,
    eval_ltD e G hA x 13 (by omega), eval_ltP e G hA x _ hC, Nat.lt_succ_iff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isStateF : (isStateF e A).eval x = true ↔ IsState e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isStateF, IsState, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 2 (by omega), eval_ltT e G hA x _ hS,
    eval_ltConst_iff A.q (nbits Qb QC) (by rw [hA.q, length_nbits]), bitsVal_nbits_of_lt QC_lt_two_pow_Qb,
    Nat.lt_succ_iff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isEmitOneF : (isEmitOneF e A).eval x = true ↔ IsEmitOne e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmitOneF, IsEmitOne, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 3 (by omega), eval_ltT e G hA x (Sof e) (by omega)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isEmitBadF : (isEmitBadF e A).eval x = true ↔ IsEmitBad e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmitBadF, IsEmitBad, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 4 (by omega), eval_ltT e G hA x (Sof e) (by omega)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_isEmittedF : (isEmittedF e A).eval x = true ↔ IsEmitted e (evalFields A x) := by
  have hS := S_succ_lt e
  simp only [isEmittedF, IsEmitted, evalFields, eval_andList_eq_true, List.forall_mem_cons,
    List.not_mem_nil, false_imp_iff, implies_true, and_true, eval_eqTag e G hA x 5 (by omega), eval_ltT e G hA x _ hS,
    Nat.lt_succ_iff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem Cand.dec_unit (c : Cand) (v : TabVar 7 6 Sym Ctl (Sof e) G) (b : Bool) :
    c.Dec e G (unit v b) ↔
      decodeVar e G c.F₁ = some v ∧ c.s₁ = b ∧ decodeVar e G c.F₂ = some v ∧ c.s₂ = b ∧
        decodeVar e G c.F₃ = some v ∧ c.s₃ = b := by
  simp only [Cand.Dec, LitDec, unit, cl]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem Cand.dec_cl (c : Cand) (l₁ l₂ l₃ : Lit (TabVar 7 6 Sym Ctl (Sof e) G)) :
    c.Dec e G (cl l₁ l₂ l₃) ↔
      decodeVar e G c.F₁ = some l₁.var ∧ c.s₁ = l₁.pos ∧ decodeVar e G c.F₂ = some l₂.var ∧
        c.s₂ = l₂.pos ∧ decodeVar e G c.F₃ = some l₃.var ∧ c.s₃ = l₃.pos := by
  simp only [Cand.Dec, LitDec, cl]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeOfCode_of_lt {k : ℕ} (h : k < 13) : ∃ d, tapeOfCode k = some d := by
  unfold tapeOfCode
  split_ifs <;> exact ⟨_, rfl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem symOfCode_of_lt {k : ℕ} (h : k < 7) : ∃ v, symOfCode k = some v := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact ⟨_, rfl⟩ | omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem qOfCode_of_lt {k : ℕ} (h : k < QC) : ∃ q, qOfCode k = some q := by
  unfold qOfCode
  rw [dif_pos h]
  exact ⟨_, rfl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeCode_lt_seven_iff (d : Tape 7 6) : tapeCode d < 7 ↔ ∃ j, d = .inl j := by
  rcases d with j | j
  · exact ⟨fun _ => ⟨j, rfl⟩, fun _ => by simp [tapeCode]⟩
  · simp [tapeCode]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- The start cell, numerically. -/
theorem startCell_val (S : ℕ) (d : Tape 7 6) :
    (startCell S d : ℕ) = if tapeCode d < 7 then 3 else S + 3 := by
  rcases d with j | j <;> simp [startCell, tapeCode]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- Boundary cells, numerically. -/
theorem isBdry_iff {S : ℕ} (p : Pos S) : p.IsBdry ↔ (p : ℕ) < 2 ∨ 2 * S + 5 ≤ p := by
  unfold Pos.IsBdry numCells
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem symCode_inputCellVal (x : List Sym) {S : ℕ} (p : Pos S) :
    symCode (inputCellVal x p) = cellCode x S p := by
  unfold inputCellVal cellCode
  by_cases hb : p.IsBdry
  · rw [if_pos hb, if_pos ((isBdry_iff p).mp hb)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ((isBdry_iff p).mpr h))]
    split_ifs <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem symCode_workCellVal₀ {S : ℕ} (p : Pos S) : symCode (workCellVal₀ (Symbol := Sym) p) = workCode S p := by
  unfold workCellVal₀ workCode
  by_cases hb : p.IsBdry
  · rw [if_pos hb, if_pos ((isBdry_iff p).mp hb)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ((isBdry_iff p).mpr h))]; rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_head {F : Fields} (h : IsHead e F) :
    ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)), decodeVar e G F = some (.head t d p) := by
  obtain ⟨hf, htag, ht, hd, hp⟩ := h
  obtain ⟨d, hd'⟩ := tapeOfCode_of_lt hd
  exact ⟨⟨F.t, by omega⟩, d, ⟨F.p, hp⟩, (decodeVar_head_iff e G F _ _ _).mpr
    ⟨⟨hf, htag, ht, hd, hp⟩, rfl, (tapeOfCode_eq_some hd').symm, rfl⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_state {F : Fields} (h : IsState e F) :
    ∃ (t : Fin (Sof e + 1)) (q : Option Ctl), decodeVar e G F = some (.state t q) := by
  obtain ⟨hf, htag, ht, hq⟩ := h
  obtain ⟨q, hq'⟩ := qOfCode_of_lt hq
  exact ⟨⟨F.t, by omega⟩, q, (decodeVar_state_iff e G F _ _).mpr
    ⟨⟨hf, htag, ht, hq⟩, rfl, (qOfCode_eq_some hq').symm⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_emitOne {F : Fields} (h : IsEmitOne e F) :
    ∃ t : Fin (Sof e), decodeVar e G F = some (.emitOne t) :=
  ⟨⟨F.t, h.2.2⟩, (decodeVar_emitOne_iff e G F _).mpr ⟨h, rfl⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_emitBad {F : Fields} (h : IsEmitBad e F) :
    ∃ t : Fin (Sof e), decodeVar e G F = some (.emitBad t) :=
  ⟨⟨F.t, h.2.2⟩, (decodeVar_emitBad_iff e G F _).mpr ⟨h, rfl⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_emitted {F : Fields} (h : IsEmitted e F) :
    ∃ t : Fin (Sof e + 1), decodeVar e G F = some (.emitted t) :=
  ⟨⟨F.t, by have := h.2.2; omega⟩, (decodeVar_emitted_iff e G F _).mpr ⟨h, rfl⟩⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_cell_congr {F F' : Fields} (h : IsCell e F) (h' : IsCell e F') (heq : cellEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h
  obtain ⟨-, h1, h2, h3, h4⟩ := (decodeVar_cell_iff e G F t d p v).mp hd
  rw [hd, eq_comm, decodeVar_cell_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2.1 ▸ h2, heq.2.2.1 ▸ h3, heq.2.2.2 ▸ h4⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem cellEq_of_decode {F F' : Fields} {t d p v} (h : decodeVar e G F = some (.cell t d p v))
    (h' : decodeVar e G F' = some (.cell t d p v)) : cellEq F F' := by
  obtain ⟨-, h1, h2, h3, h4⟩ := (decodeVar_cell_iff e G F t d p v).mp h
  obtain ⟨-, h1', h2', h3', h4'⟩ := (decodeVar_cell_iff e G F' t d p v).mp h'
  exact ⟨by omega, by omega, by omega, by omega⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_head_congr {F F' : Fields} (h : IsHead e F) (h' : IsHead e F') (heq : headEq F F') :
    decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, d, p, hd⟩ := exists_head e G h
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_head_iff e G F t d p).mp hd
  rw [hd, eq_comm, decodeVar_head_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2.1 ▸ h2, heq.2.2 ▸ h3⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem headEq_of_decode {F F' : Fields} {t d p} (h : decodeVar e G F = some (.head t d p))
    (h' : decodeVar e G F' = some (.head t d p)) : headEq F F' := by
  obtain ⟨-, h1, h2, h3⟩ := (decodeVar_head_iff e G F t d p).mp h
  obtain ⟨-, h1', h2', h3'⟩ := (decodeVar_head_iff e G F' t d p).mp h'
  exact ⟨by omega, by omega, by omega⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_state_congr {F F' : Fields} (h : IsState e F) (h' : IsState e F')
    (heq : stateEq F F') : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, q, hd⟩ := exists_state e G h
  obtain ⟨-, h1, h2⟩ := (decodeVar_state_iff e G F t q).mp hd
  rw [hd, eq_comm, decodeVar_state_iff]
  exact ⟨h', heq.1 ▸ h1, heq.2 ▸ h2⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem stateEq_of_decode {F F' : Fields} {t q} (h : decodeVar e G F = some (.state t q))
    (h' : decodeVar e G F' = some (.state t q)) : stateEq F F' := by
  obtain ⟨-, h1, h2⟩ := (decodeVar_state_iff e G F t q).mp h
  obtain ⟨-, h1', h2'⟩ := (decodeVar_state_iff e G F' t q).mp h'
  exact ⟨by omega, by omega⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_emitBad_congr {F F' : Fields} (h : IsEmitBad e F) (h' : IsEmitBad e F')
    (heq : F.t = F'.t) : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, hd⟩ := exists_emitBad e G h
  obtain ⟨-, h1⟩ := (decodeVar_emitBad_iff e G F t).mp hd
  rw [hd, eq_comm, decodeVar_emitBad_iff]
  exact ⟨h', heq ▸ h1⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem decodeVar_emitted_congr {F F' : Fields} (h : IsEmitted e F) (h' : IsEmitted e F')
    (heq : F.t = F'.t) : decodeVar e G F = decodeVar e G F' := by
  obtain ⟨t, hd⟩ := exists_emitted e G h
  obtain ⟨-, h1⟩ := (decodeVar_emitted_iff e G F t).mp hd
  rw [hd, eq_comm, decodeVar_emitted_iff]
  exact ⟨h', heq ▸ h1⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem symCode_inj {v v' : CellVal Sym} : symCode v = symCode v' ↔ v = v' :=
  ⟨fun h => by
    have := symOfCode_symCode v
    rw [h, symOfCode_symCode] at this
    exact (Option.some.inj this).symm, fun h => h ▸ rfl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem qCode_inj {q q' : Option Ctl} : qCode q = qCode q' ↔ q = q' := by
  unfold qCode
  rw [Fin.val_inj]
  exact (Fintype.equivFin (Option Ctl)).injective.eq_iff
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeCode_inl (j : Fin 7) : tapeCode (.inl j) = j := rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem tapeCode_inr (j : Fin 6) : tapeCode (.inr j) = 7 + j := rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem seven_le_tapeCode_iff (d : Tape 7 6) : 7 ≤ tapeCode d ↔ ∃ j, d = .inr j := by
  rcases d with j | j
  · simp [tapeCode]
  · exact ⟨fun _ => ⟨j, rfl⟩, fun _ => by simp [tapeCode]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_cell (c : Cand) (t d p v) (b : Bool) :
    c.Dec e G (unit (.cell t d p v) b) ↔
      decodeVar e G c.F₁ = some (.cell t d p v) ∧ UnitCell e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_cell_iff e G _ _ _ _ _).mp h₁).1, ((decodeVar_cell_iff e G _ _ _ _ _).mp h₂).1,
      ((decodeVar_cell_iff e G _ _ _ _ _).mp h₃).1, cellEq_of_decode e G h₁ h₂, cellEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_cell_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_cell_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_head (c : Cand) (t d p) (b : Bool) :
    c.Dec e G (unit (.head t d p) b) ↔
      decodeVar e G c.F₁ = some (.head t d p) ∧ UnitHead e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_head_iff e G _ _ _ _).mp h₁).1, ((decodeVar_head_iff e G _ _ _ _).mp h₂).1,
      ((decodeVar_head_iff e G _ _ _ _).mp h₃).1, headEq_of_decode e G h₁ h₂, headEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_head_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_head_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_state (c : Cand) (t q) (b : Bool) :
    c.Dec e G (unit (.state t q) b) ↔
      decodeVar e G c.F₁ = some (.state t q) ∧ UnitState e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    exact ⟨h₁, ⟨((decodeVar_state_iff e G _ _ _).mp h₁).1, ((decodeVar_state_iff e G _ _ _).mp h₂).1,
      ((decodeVar_state_iff e G _ _ _).mp h₃).1, stateEq_of_decode e G h₁ h₂, stateEq_of_decode e G h₁ h₃⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_state_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_state_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_emitBad (c : Cand) (t) (b : Bool) :
    c.Dec e G (unit (.emitBad t) b) ↔
      decodeVar e G c.F₁ = some (.emitBad t) ∧ UnitEmitBad e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    have k₁ := (decodeVar_emitBad_iff e G _ _).mp h₁
    have k₂ := (decodeVar_emitBad_iff e G _ _).mp h₂
    have k₃ := (decodeVar_emitBad_iff e G _ _).mp h₃
    exact ⟨h₁, ⟨k₁.1, k₂.1, k₃.1, by rw [k₁.2, k₂.2], by rw [k₁.2, k₃.2]⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_emitBad_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_emitBad_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem dec_unit_emitted (c : Cand) (t) (b : Bool) :
    c.Dec e G (unit (.emitted t) b) ↔
      decodeVar e G c.F₁ = some (.emitted t) ∧ UnitEmitted e c ∧ c.s₁ = b ∧ SameSigns c := by
  rw [Cand.dec_unit]
  constructor
  · rintro ⟨h₁, hs₁, h₂, hs₂, h₃, hs₃⟩
    have k₁ := (decodeVar_emitted_iff e G _ _).mp h₁
    have k₂ := (decodeVar_emitted_iff e G _ _).mp h₂
    have k₃ := (decodeVar_emitted_iff e G _ _).mp h₃
    exact ⟨h₁, ⟨k₁.1, k₂.1, k₃.1, by rw [k₁.2, k₂.2], by rw [k₁.2, k₃.2]⟩,
      hs₁, by rw [hs₂, hs₁], by rw [hs₃, hs₁]⟩
  · rintro ⟨h₁, ⟨k₁, k₂, k₃, e₂, e₃⟩, hs₁, hs₂, hs₃⟩
    exact ⟨h₁, hs₁, by rw [← decodeVar_emitted_congr e G k₁ k₂ e₂]; exact h₁, by rw [hs₂, hs₁],
      by rw [← decodeVar_emitted_congr e G k₁ k₃ e₃]; exact h₁, by rw [hs₃, hs₁]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem exists_mem_union {α : Type*} (A B : Set α) (P : α → Prop) :
    (∃ x ∈ A ∪ B, P x) ↔ (∃ x ∈ A, P x) ∨ (∃ x ∈ B, P x) := by
  simp only [Set.mem_union, or_and_right, exists_or]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem startHead_iff (c : Cand) :
    StartHead e c ↔ ∃ cl ∈ ({cl | ∃ d p, cl = unit (.head 0 d p) (decide (p = startCell (Sof e) d))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, d, p, hd⟩ := exists_head e G hu.1
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ t d p).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    refine ⟨_, ⟨d, p, rfl⟩, (dec_unit_head e G c _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff, startCell_val, ← hpp, ← hdd]
  · rintro ⟨_, ⟨d, p, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_head e G c _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ _ d p).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [Fin.ext_iff, startCell_val, ← hpp, ← hdd]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem startState_iff (c : Cand) :
    StartState e c ↔ ∃ cl ∈ ({cl | ∃ q, cl = unit (.state 0 q) (decide (q = some U.q₀))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, q, hd⟩ := exists_state e G hu.1
    obtain ⟨-, htt, hqq⟩ := (decodeVar_state_iff e G _ t q).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    refine ⟨_, ⟨q, rfl⟩, (dec_unit_state e G c _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [hqq, qCode_inj]
  · rintro ⟨_, ⟨q, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_state e G c _ _ _).mp hdec
    obtain ⟨-, htt, hqq⟩ := (decodeVar_state_iff e G _ _ q).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [hqq, qCode_inj]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem startFixed_iff (c : Cand) :
    StartFixed e fixed c ↔ ∃ cl ∈ ({cl | ∃ j x p v, fixed j = some x ∧
      cl = unit (.cell 0 (.inl j) p v) (decide (v = inputCellVal x p))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, j, x, hx, hj, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hj]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', x, p, v, hx, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_inputCellVal, ← hvv, ← hpp]
  · rintro ⟨_, ⟨j, x, p, v, hx, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], j, x, hx, by rw [hdd, tapeCode_inl], ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_inputCellVal, ← hvv, ← hpp]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem startWork_iff (c : Cand) :
    StartWork e c ↔ ∃ cl ∈ ({cl | ∃ j p v, cl = unit (.cell 0 (.inr j) p v) (decide (v = workCellVal₀ p))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hj, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j, rfl⟩ := (seven_le_tapeCode_iff d).mp (by omega)
    refine ⟨_, ⟨j, p, v, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_workCellVal₀, ← hvv, ← hpp]
  · rintro ⟨_, ⟨j, p, v, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], by rw [hdd, tapeCode_inr]; omega, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, symCode_workCellVal₀, ← hvv, ← hpp]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem startPred_iff (c : Cand) :
    StartPred e fixed c ↔ ∃ cl ∈ startClauses (S := Sof e) (G := G) U fixed, c.Dec e G cl := by
  unfold startClauses StartPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, ← startHead_iff, ← startState_iff,
    ← startFixed_iff, ← startWork_iff]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeBdry_iff (c : Cand) :
    FreeBdry e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v, fixed j = none ∧ p.IsBdry ∧
      cl = unit (.cell 0 (.inl j) p v) (decide (v = .bdry))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hb, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', p, v, hj, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨j, p, v, hj, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩,
      by rw [hpp]; exact (isBdry_iff p).mp hb, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeOther_iff (c : Cand) :
    FreeOther e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v, fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ .sym .zero ∧
      v ≠ .sym .one ∧ v ≠ .blank ∧ cl = unit (.cell 0 (.inl j) p v) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hb, h0, h1, h5, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    refine ⟨_, ⟨j', p, v, hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h), ?_, ?_, ?_, rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, hs, hss⟩⟩
    · rintro rfl; exact h0 hvv
    · rintro rfl; exact h1 hvv
    · rintro rfl; exact h5 hvv
  · rintro ⟨_, ⟨j, p, v, hj, hb, h0, h1, h5, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← hpp]; exact h)), ?_, ?_, ?_, hs⟩
    · rw [hvv]; intro h; exact h0 (symCode_inj.mp h)
    · rw [hvv]; intro h; exact h1 (symCode_inj.mp h)
    · rw [hvv]; intro h; exact h5 (symCode_inj.mp h)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeTwo_iff (c : Cand) :
    FreeTwo e fixed c ↔ ∃ cl ∈ ({cl | ∃ j v, fixed j = none ∧
      cl = unit (.cell 0 (.inl j) ⟨2, by unfold numCells; omega⟩ v) (decide (v = .blank))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, ⟨j, hj, hjd⟩, hp, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hp2 : p = ⟨2, by unfold numCells; omega⟩ := Fin.ext (by simp; omega)
    rw [hp2] at hd
    refine ⟨_, ⟨j', v, hj, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨j, v, hj, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ _ v).mp hd
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ⟨j, hj, by rw [hdd, tapeCode_inl]⟩, hpp, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeOneOf_iff (c : Cand) :
    FreeOneOf e fixed c ↔ ∃ c' ∈ ({c' | ∃ (j : Fin 7) (p : Pos (Sof e)), fixed j = none ∧ ¬ p.IsBdry ∧
      c' = cl ⟨.cell 0 (.inl j) p (.sym .zero), true⟩ ⟨.cell 0 (.inl j) p (.sym .one), true⟩
        ⟨.cell 0 (.inl j) p .blank, true⟩} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, ⟨t₂, d₂, p₂⟩, ⟨t₃, d₃, p₃⟩, ht, ⟨j, hj, hjd⟩, hb, v₁, v₂, v₃, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hv : v = .sym .zero := symCode_inj.mp (by rw [← hvv, v₁]; rfl)
    subst hv
    refine ⟨_, ⟨j', p, hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h), rfl⟩,
      (Cand.dec_cl e G c _ _ _).mpr ⟨hd, s₁, ?_, s₂, ?_, s₃⟩⟩
    · exact (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [← t₂, htt], by rw [← d₂, hdd],
        by rw [← p₂, hpp], v₂⟩
    · exact (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₃, by rw [← t₃, htt], by rw [← d₃, hdd],
        by rw [← p₃, hpp], v₃⟩
  · rintro ⟨_, ⟨j, p, hj, hb, rfl⟩, hdec⟩
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e G c _ _ _).mp hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    obtain ⟨h₃, t₃, d₃, p₃, v₃⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₃
    refine ⟨h₁, h₂, h₃, ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩,
      by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← p₁]; exact h)), v₁, v₂, v₃, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeNand_iff (c : Cand) :
    FreeNand e fixed c ↔ ∃ cl ∈ ({cl | ∃ j p v v', fixed j = none ∧ ¬ p.IsBdry ∧ v ≠ v' ∧
      cl = nand2 (.cell 0 (.inl j) p v) (.cell 0 (.inl j) p v')} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨h₁, h₂, h₃, ⟨t₂, d₂, p₂⟩, e₂₃, ht, ⟨j, hj, hjd⟩, hb, hne, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    obtain ⟨v', hv'⟩ := symOfCode_of_lt (show c.F₂.v < 7 by
      rcases h₂ with ⟨-, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, h⟩ <;> exact h)
    have hvv' := symOfCode_eq_some hv'
    have hd₂ : decodeVar e G c.F₂ = some (.cell 0 (.inl j') p v') :=
      (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [← t₂, htt], by rw [← d₂, hdd],
        by rw [← p₂, hpp], hvv'.symm⟩
    refine ⟨_, ⟨j', p, v, v', hj, fun h => hb (by rw [hpp]; exact (isBdry_iff p).mp h),
      fun h => hne (by rw [hvv, ← hvv', h]), rfl⟩, ?_⟩
    simp only [nand2, Cand.dec_cl]
    exact ⟨hd, s₁, hd₂, s₂, by rw [← decodeVar_cell_congr e G h₂ h₃ e₂₃]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨j, p, v, v', hj, hb, hne, rfl⟩, hdec⟩
    simp only [nand2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    refine ⟨h₁, h₂, ((decodeVar_cell_iff e G _ _ _ _ _).mp hd₃).1, ⟨by omega, by omega, by omega⟩,
      cellEq_of_decode e G hd₂ hd₃, by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩,
      fun h => hb ((isBdry_iff p).mpr (by rw [← p₁]; exact h)), ?_, s₁, s₂, s₃⟩
    rw [v₁, v₂]
    exact fun h => hne (symCode_inj.mp h)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freeBlank_iff (c : Cand) :
    FreeBlank e fixed c ↔ ∃ cl ∈ ({cl | ∃ (j : Fin 7) (p p' : Pos (Sof e)), fixed j = none ∧ 2 < (p : ℕ) ∧
      ¬ p'.IsBdry ∧ p < p' ∧ cl = imp2 (.cell 0 (.inl j) p .blank) (.cell 0 (.inl j) p' .blank)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨h₁, h₂, h₃, e₂₃, ht, ⟨j, hj, hjd⟩, t₂, d₂, hp2, hb, hlt, v₁, v₂, s₁, s₂, s₃⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G h₁
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j', rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd, hjd]; exact j.isLt)
    have hj' : j' = j := Fin.ext (by rw [tapeCode_inl] at hdd; omega)
    subst hj'
    have hv : v = .blank := symCode_inj.mp (by rw [← hvv, v₁]; rfl)
    subst hv
    have hp' : c.F₂.p < numCells (Sof e) := by
      rcases h₂ with ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, -, -, h, -⟩ <;> exact h
    have hd₂ : decodeVar e G c.F₂ = some (.cell 0 (.inl j') ⟨c.F₂.p, hp'⟩ .blank) :=
      (decodeVar_cell_iff e G _ _ _ _ _).mpr ⟨h₂, by rw [t₂, htt], by rw [d₂, hdd], rfl, v₂⟩
    refine ⟨_, ⟨j', p, ⟨c.F₂.p, hp'⟩, hj, by omega, fun h => hb ((isBdry_iff _).mp h),
      by rw [Fin.lt_iff_val_lt_val, ← hpp]; exact hlt, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    exact ⟨hd, s₁, hd₂, s₂, by rw [← decodeVar_cell_congr e G h₂ h₃ e₂₃]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨j, p, p', hj, hp2, hb, hlt, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁, d₁, p₁, v₁⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₁
    obtain ⟨h₂, t₂, d₂, p₂, v₂⟩ := (decodeVar_cell_iff e G _ _ _ _ _).mp hd₂
    refine ⟨h₁, h₂, ((decodeVar_cell_iff e G _ _ _ _ _).mp hd₃).1, cellEq_of_decode e G hd₂ hd₃,
      by rw [t₁, Fin.val_zero], ⟨j, hj, by rw [d₁, tapeCode_inl]⟩, by rw [t₁, t₂], by rw [d₁, d₂],
      by omega, fun h => hb ((isBdry_iff p').mpr (by rw [← p₂]; exact h)),
      by rw [p₁, p₂]; exact hlt, v₁, v₂, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem freePred_iff (c : Cand) :
    FreePred e fixed c ↔ ∃ cl ∈ freeClauses (S := Sof e) (G := G) Sym.zero Sym.one fixed, c.Dec e G cl := by
  unfold freeClauses FreePred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union,
    ← freeBdry_iff, ← freeOther_iff, ← freeTwo_iff, ← freeOneOf_iff, ← freeNand_iff, ← freeBlank_iff]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem bdryCell_iff (c : Cand) :
    BdryCell e c ↔ ∃ cl ∈ ({cl | ∃ t d p v, p.IsBdry ∧ cl = unit (.cell t d p v) (decide (v = .bdry))} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hb, hs⟩
    obtain ⟨t, d, p, v, hd⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hd
    refine ⟨_, ⟨t, d, p, v, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hd, hu, ?_, hss⟩⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
  · rintro ⟨_, ⟨t, d, p, v, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p v).mp hd
    refine ⟨hu, hss, by rw [hpp]; exact (isBdry_iff p).mp hb, ?_⟩
    rw [hs]
    apply decide_eq_decide.mpr
    rw [← symCode_inj, ← hvv]
    rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem bdryHead_iff (c : Cand) :
    BdryHead e c ↔ ∃ cl ∈ ({cl | ∃ t d p, p.IsBdry ∧ cl = unit (.head t d p) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hb, hs⟩
    obtain ⟨t, d, p, hd⟩ := exists_head e G hu.1
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ t d p).mp hd
    exact ⟨_, ⟨t, d, p, (isBdry_iff p).mpr (by rw [← hpp]; exact hb), rfl⟩,
      (dec_unit_head e G c _ _ _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, ⟨t, d, p, hb, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_head e G c _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp⟩ := (decodeVar_head_iff e G _ _ _ p).mp hd
    exact ⟨hu, hss, by rw [hpp]; exact (isBdry_iff p).mp hb, hs⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem bdryPred_iff (c : Cand) :
    BdryPred e c ↔ ∃ cl ∈ bdryClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold bdryClauses BdryPred
  rw [exists_mem_union, ← bdryCell_iff, ← bdryHead_iff]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitZero_iff (c : Cand) :
    EmitZero e c ↔ ∃ cl ∈ ({unit (.emitted 0) false} : Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)),
      c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hs⟩
    obtain ⟨t, hd⟩ := exists_emitted e G hu.1
    obtain ⟨-, htt⟩ := (decodeVar_emitted_iff e G _ t).mp hd
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    exact ⟨_, rfl, (dec_unit_emitted e G c _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, rfl, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_emitted e G c _ _).mp hdec
    obtain ⟨-, htt⟩ := (decodeVar_emitted_iff e G _ _).mp hd
    exact ⟨hu, hss, by rw [htt, Fin.val_zero], hs⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitStep_iff (c : Cand) :
    EmitStep e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e),
      c' = cl ⟨.emitted t.succ, false⟩ ⟨.emitted t.castSucc, true⟩ ⟨.emitOne t, true⟩} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₁, t₂, s₁, s₂, s₃⟩
    obtain ⟨t, hd₃⟩ := exists_emitOne e G h₃
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₃
    refine ⟨_, ⟨t, rfl⟩, (Cand.dec_cl e G c _ _ _).mpr ⟨?_, s₁, ?_, s₂, hd₃, s₃⟩⟩
    · exact (decodeVar_emitted_iff e G _ _).mpr ⟨h₁, by rw [Fin.val_succ, ← htt, t₁]⟩
    · exact (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.coe_castSucc, ← htt, t₂]⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := (Cand.dec_cl e G c _ _ _).mp hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitted_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₃
    rw [Fin.val_succ] at t₁
    rw [Fin.coe_castSucc] at t₂
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitMono_iff (c : Cand) :
    EmitMono e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = imp2 (.emitted t.castSucc) (.emitted t.succ)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, hlt, t₂, t₃, s₁, s₂, s₃⟩
    have hd₂ : decodeVar e G c.F₂ = some (.emitted (⟨c.F₁.t, hlt⟩ : Fin (Sof e)).succ) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.val_succ, t₂]⟩
    refine ⟨_, ⟨⟨c.F₁.t, hlt⟩, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    refine ⟨(decodeVar_emitted_iff e G _ _).mpr ⟨h₁, by rw [Fin.coe_castSucc]⟩, s₁, hd₂, s₂,
      by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitted_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.coe_castSucc] at t₁
    rw [Fin.val_succ] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by rw [t₁]; exact t.isLt, by omega, by omega, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitOne_iff (c : Cand) :
    EmitOne e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = imp2 (.emitOne t) (.emitted t.succ)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₂, t₃, s₁, s₂, s₃⟩
    obtain ⟨t, hd₁⟩ := exists_emitOne e G h₁
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₁
    have hd₂ : decodeVar e G c.F₂ = some (.emitted t.succ) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.val_succ, ← htt, t₂]⟩
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    simp only [imp2, Cand.dec_cl]
    exact ⟨hd₁, s₁, hd₂, s₂, by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [imp2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.val_succ] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitOnce_iff (c : Cand) :
    EmitOnce e c ↔ ∃ c' ∈ ({c' | ∃ t : Fin (Sof e), c' = nand2 (.emitOne t) (.emitted t.castSucc)} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G c' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, t₂, t₃, s₁, s₂, s₃⟩
    obtain ⟨t, hd₁⟩ := exists_emitOne e G h₁
    obtain ⟨-, htt⟩ := (decodeVar_emitOne_iff e G _ t).mp hd₁
    have hd₂ : decodeVar e G c.F₂ = some (.emitted t.castSucc) :=
      (decodeVar_emitted_iff e G _ _).mpr ⟨h₂, by rw [Fin.coe_castSucc, ← htt, t₂]⟩
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    simp only [nand2, Cand.dec_cl]
    exact ⟨hd₁, s₁, hd₂, s₂, by rw [← decodeVar_emitted_congr e G h₂ h₃ t₃.symm]; exact hd₂, s₃⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    simp only [nand2, Cand.dec_cl] at hdec
    obtain ⟨hd₁, s₁, hd₂, s₂, hd₃, s₃⟩ := hdec
    obtain ⟨h₁, t₁⟩ := (decodeVar_emitOne_iff e G _ _).mp hd₁
    obtain ⟨h₂, t₂⟩ := (decodeVar_emitted_iff e G _ _).mp hd₂
    obtain ⟨h₃, t₃⟩ := (decodeVar_emitted_iff e G _ _).mp hd₃
    rw [Fin.coe_castSucc] at t₂ t₃
    exact ⟨h₁, h₂, h₃, by omega, by omega, s₁, s₂, s₃⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitBad_iff (c : Cand) :
    EmitBad e c ↔ ∃ cl ∈ ({cl | ∃ t : Fin (Sof e), cl = unit (.emitBad t) false} :
      Cnf3 (TabVar 7 6 Sym Ctl (Sof e) G)), c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, hs⟩
    obtain ⟨t, hd⟩ := exists_emitBad e G hu.1
    exact ⟨_, ⟨t, rfl⟩, (dec_unit_emitBad e G c _ _).mpr ⟨hd, hu, hs, hss⟩⟩
  · rintro ⟨_, ⟨t, rfl⟩, hdec⟩
    obtain ⟨hd, hu, hs, hss⟩ := (dec_unit_emitBad e G c _ _).mp hdec
    exact ⟨hu, hss, hs⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem emitPred_iff (c : Cand) :
    EmitPred e c ↔ ∃ cl ∈ emitClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold emitClauses EmitPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union,
    ← emitZero_iff, ← emitStep_iff, ← emitMono_iff, ← emitOne_iff, ← emitOnce_iff, ← emitBad_iff]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
theorem finalPred_iff (c : Cand) :
    FinalPred e c ↔ ∃ cl ∈ finalClauses (i := 7) (w := 6) (Symbol := Sym) (State := Ctl) (S := Sof e) (G := G),
      c.Dec e G cl := by
  unfold finalClauses FinalPred FinalState FinalEmitted
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, exists_or, exists_eq_left,
    dec_unit_state, dec_unit_emitted]
  constructor
  · rintro (⟨hu, hss, ht, hq, hs⟩ | ⟨hu, hss, ht, hs⟩)
    · exact Or.inl ⟨(decodeVar_state_iff e G _ _ _).mpr ⟨hu.1, by rw [Fin.val_last]; exact ht, hq⟩,
        hu, hs, hss⟩
    · exact Or.inr ⟨(decodeVar_emitted_iff e G _ _).mpr ⟨hu.1, by rw [Fin.val_last]; exact ht⟩,
        hu, hs, hss⟩
  · rintro (⟨hd, hu, hs, hss⟩ | ⟨hd, hu, hs, hss⟩)
    · obtain ⟨-, ht, hq⟩ := (decodeVar_state_iff e G _ _ _).mp hd
      exact Or.inl ⟨hu, hss, by rw [ht, Fin.val_last], hq, hs⟩
    · obtain ⟨-, ht⟩ := (decodeVar_emitted_iff e G _ _).mp hd
      exact Or.inr ⟨hu, hss, by rw [ht, Fin.val_last], hs⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym))
/-- The candidate decodes to a clause of the five explicit families iff `MainPred`. -/
theorem mainPred_iff (c : Cand) :
    MainPred e fixed c ↔ ∃ cl ∈ startClauses (S := Sof e) (G := G) U fixed ∪
      freeClauses (S := Sof e) (G := G) Sym.zero Sym.one fixed ∪ bdryClauses (S := Sof e) (G := G) ∪
      emitClauses (S := Sof e) (G := G) ∪ finalClauses (S := Sof e) (G := G), c.Dec e G cl := by
  unfold MainPred
  rw [exists_mem_union, exists_mem_union, exists_mem_union, exists_mem_union, ← startPred_iff,
    ← freePred_iff, ← bdryPred_iff, ← emitPred_iff, ← finalPred_iff]
  tauto
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable {S G : ℕ}
/-- A spec of a template of gate `g` is the gate, a gate it reads, or the input it reads. -/
theorem spec_of_templates (g : ℕ) (gate : Gate) (tp : Tpl) (h : tp ∈ gateTemplates g gate)
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ (u = g ∨ u ∈ gate.refs)) ∨ (∃ i, sp = .win i ∧ gate = .input i) := by
  cases gate <;> simp only [gateTemplates, List.mem_cons, List.not_mem_nil, or_false] at h <;>
    rcases h with rfl | rfl | rfl | rfl <;> rcases hsp with rfl | rfl | rfl <;> simp [Gate.refs]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])
include hC hin hinp in
/-- The specs of a template of a gate of `chk` are in range. -/
theorem spec_lt (g : Fin chk.gates.length) (tp : Tpl) (h : tp ∈ gateTemplates g chk.gates[g])
    (sp : LitSpec) (hsp : sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) :
    (∃ u, sp = .aux u ∧ u < chk.gates.length) ∨ (∃ i, sp = .win i ∧ i < winCard 7 6 Sym Ctl) := by
  rcases spec_of_templates g _ tp h sp hsp with ⟨u, rfl, rfl | hu⟩ | ⟨i, rfl, hi⟩
  · exact Or.inl ⟨_, rfl, g.isLt⟩
  · exact Or.inl ⟨u, rfl, lt_trans (hC g g.isLt u hu) g.isLt⟩
  · exact Or.inr ⟨i, rfl, hinp ▸ hin i (hi ▸ List.getElem_mem g.isLt)⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
/-- The candidate decodes to a clause of the tableau iff it satisfies one of the family
predicates. -/
theorem tableau_dec_iff (fixed : Fin 7 → Option (List Sym)) (chk : Circuit) (hC : chk.RefsLt)
    (hin : chk.InputsLt) (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ []) (c : Cand) :
    (MainPred e fixed c ∨ WindowPred e chk.gates.length chk c) ↔
      ∃ cl ∈ tableau U Sym.zero Sym.one (Sof e) fixed chk, c.Dec e chk.gates.length cl := by
  unfold tableau
  rw [exists_mem_union, ← mainPred_iff, ← windowPred_iff e chk hC hin hinp hne]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem Bool.eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) :
    b = decide P := by
  cases b
  · simp only [Bool.false_eq_true, false_iff] at h
    simp [h]
  · simp only [true_iff] at h
    simp [h]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_eqN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (eqConst fs (nbits w k)).eval x = true ↔ val fs x = k := by
  rw [eval_eqConst_iff _ _ (by rw [hl, length_nbits]), bitsVal_nbits_of_lt hk]
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
theorem eval_ltF {fs gs : List Fml} {w : ℕ} (hl : fs.length = w) (hg : gs.length = w) (x : ℕ → Bool) :
    (ltFields fs gs).eval x = true ↔ val fs x < val gs x :=
  eval_ltFields_iff _ _ (by rw [hl, hg]) x
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
theorem eval_xnor_iff (f g : Fml) (x : ℕ → Bool) : (xnor f g).eval x = true ↔ f.eval x = g.eval x := by
  rw [eval_xnor, beq_iff_eq]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_sign (σ f : Fml) (x : ℕ → Bool) {P : Prop} [Decidable P] (hf : f.eval x = true ↔ P) :
    (xnor σ f).eval x = true ↔ σ.eval x = decide P := by
  rw [eval_xnor_iff, Bool.eq_decide_of_iff hf]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_signConst (σ : Fml) (b : Bool) (x : ℕ → Bool) :
    (xnor σ (const b)).eval x = true ↔ σ.eval x = b := by
  rw [eval_xnor_iff]; rfl
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
theorem eval_and_iff (f g : Fml) (x : ℕ → Bool) : (and f g).eval x = true ↔ f.eval x = true ∧ g.eval x = true := by
  simp [eval]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_or_iff (f g : Fml) (x : ℕ → Bool) : (or f g).eval x = true ↔ f.eval x = true ∨ g.eval x = true := by
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
theorem eval_andList₄ (a b c d : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₅ (a b c d f : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₆ (a b c d f g : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₇ (a b c d f g h : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₈ (a b c d f g h i : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h, i]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true ∧ i.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem eval_andList₉ (a b c d f g h i j : Fml) (x : ℕ → Bool) :
    (andList [a, b, c, d, f, g, h, i, j]).eval x = true ↔
      a.eval x = true ∧ b.eval x = true ∧ c.eval x = true ∧ d.eval x = true ∧ f.eval x = true ∧
        g.eval x = true ∧ h.eval x = true ∧ i.eval x = true ∧ j.eval x = true := by
  simp [eval_andList_eq_true]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_cellEqF : (cellEqF A B).eval x = true ↔ cellEq (evalFields A x) (evalFields B x) := by
  rw [cellEqF, eval_andList₄, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p, eval_eqF hA.v hB.v]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_headEqF : (headEqF A B).eval x = true ↔ headEq (evalFields A x) (evalFields B x) := by
  rw [headEqF, eval_andList₃, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_stateEqF : (stateEqF A B).eval x = true ↔ stateEq (evalFields A x) (evalFields B x) := by
  rw [stateEqF, eval_andList₂, eval_eqF hA.t hB.t, eval_eqF hA.q hB.q]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_samePosF : (samePosF A B).eval x = true ↔ samePos (evalFields A x) (evalFields B x) := by
  rw [samePosF, eval_andList₃, eval_eqF hA.t hB.t, eval_eqF hA.d hB.d, eval_eqF hA.p hB.p]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_tEqF : (eqFields A.t B.t).eval x = true ↔ (evalFields A x).t = (evalFields B x).t :=
  eval_eqF hA.t hB.t x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A B : FieldsF} (hA : A.Lengths e G) (hB : B.Lengths e G) (x : ℕ → Bool)
include hA hB
theorem eval_auxEqF : (auxEqF A B).eval x = true ↔ auxEq (evalFields A x) (evalFields B x) := by
  simp only [auxEqF, eval_andList_eq_true, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false, auxEq, evalFields]
  constructor
  · intro h
    exact ⟨(eval_eqF hA.t hB.t x).mp (h _ (Or.inl (Or.inl rfl))),
      fun k => (eval_eqF (hA.js k) (hB.js k) x).mp (h _ (Or.inr ⟨k, rfl⟩)),
      (eval_eqF hA.g hB.g x).mp (h _ (Or.inl (Or.inr rfl)))⟩
  · rintro ⟨h1, h2, h3⟩ f hf
    rcases hf with (rfl | rfl) | ⟨k, rfl⟩
    · exact (eval_eqF hA.t hB.t x).mpr h1
    · exact (eval_eqF hA.g hB.g x).mpr h3
    · exact (eval_eqF (hA.js k) (hB.js k) x).mpr (h2 k)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitCellF : (unitCellF e C).eval x = true ↔ UnitCell e (evalCand C x) := by
  rw [unitCellF, eval_andList₅, eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃,
    eval_cellEqF e G hC.A₁ hC.A₂, eval_cellEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitHeadF : (unitHeadF e C).eval x = true ↔ UnitHead e (evalCand C x) := by
  rw [unitHeadF, eval_andList₅, eval_isHeadF e G hC.A₁, eval_isHeadF e G hC.A₂, eval_isHeadF e G hC.A₃,
    eval_headEqF e G hC.A₁ hC.A₂, eval_headEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitStateF : (unitStateF e C).eval x = true ↔ UnitState e (evalCand C x) := by
  rw [unitStateF, eval_andList₅, eval_isStateF e G hC.A₁, eval_isStateF e G hC.A₂, eval_isStateF e G hC.A₃,
    eval_stateEqF e G hC.A₁ hC.A₂, eval_stateEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitEmitBadF : (unitEmitBadF e C).eval x = true ↔ UnitEmitBad e (evalCand C x) := by
  rw [unitEmitBadF, eval_andList₅, eval_isEmitBadF e G hC.A₁, eval_isEmitBadF e G hC.A₂,
    eval_isEmitBadF e G hC.A₃, eval_tEqF e G hC.A₁ hC.A₂, eval_tEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitEmittedF : (unitEmittedF e C).eval x = true ↔ UnitEmitted e (evalCand C x) := by
  rw [unitEmittedF, eval_andList₅, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂,
    eval_isEmittedF e G hC.A₃, eval_tEqF e G hC.A₁ hC.A₂, eval_tEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_unitAuxF : (unitAuxF e G C).eval x = true ↔ UnitAux e G (evalCand C x) := by
  rw [unitAuxF, eval_andList₅, eval_isAuxF e G hC.A₁, eval_isAuxF e G hC.A₂, eval_isAuxF e G hC.A₃,
    eval_auxEqF e G hC.A₁ hC.A₂, eval_auxEqF e G hC.A₁ hC.A₃]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
omit hC in
theorem eval_sameSignsF : (sameSignsF C).eval x = true ↔ SameSigns (evalCand C x) := by
  rw [sameSignsF, eval_and_iff, eval_xnor_iff, eval_xnor_iff]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem twoS5_lt : 2 * Sof e + 5 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem S_lt_two_pow : Sof e < 2 ^ W e := by have := twoS5_lt e; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_bdryF : (bdryF e A).eval x = true ↔ Bdry (Sof e) (evalFields A x).p := by
  rw [bdryF, eval_or_iff, eval_not_iff, eval_ltN hA.p (by have := twoS5_lt e; omega),
    eval_ltN hA.p (twoS5_lt e)]
  dsimp only [evalFields]
  simp only [not_lt]
  exact Iff.rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_startCellF :
    (startCellF e A).eval x = true ↔
      (evalFields A x).p = if (evalFields A x).d < 7 then 3 else Sof e + 3 := by
  have hS := twoS5_lt e
  rw [startCellF, eval_mux]
  have h7 : (ltConst A.d (nbits 4 7)).eval x = decide (val A.d x < 7) :=
    Bool.eq_decide_of_iff (eval_ltN hA.d (by norm_num) x)
  rw [h7]
  show _ ↔ val A.p x = if val A.d x < 7 then 3 else Sof e + 3
  by_cases h : val A.d x < 7
  · rw [if_pos (by simpa using h), if_pos h]; exact eval_eqN hA.p (by omega) x
  · rw [if_neg (by simpa using h), if_neg h]; exact eval_eqN hA.p (by omega) x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem eval_workValF :
    (workValF e A).eval x = true ↔ (evalFields A x).v = workCode (Sof e) (evalFields A x).p := by
  rw [workValF, eval_mux, workCode]
  by_cases hb : Bdry (Sof e) (evalFields A x).p
  · rw [if_pos ((eval_bdryF e G hA x).mpr hb),
      if_pos (show (evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p from hb)]
    exact eval_eqN (k := 6) hA.v (by norm_num) x
  · rw [if_neg (fun h => hb ((eval_bdryF e G hA x).mp h)),
      if_neg (show ¬ ((evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p) from hb)]
    exact eval_eqN (k := 5) hA.v (by norm_num) x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem eval_andList_cons (a : Fml) (l : List Fml) (x : ℕ → Bool) :
    (andList (a :: l)).eval x = true ↔ a.eval x = true ∧ (andList l).eval x = true := by
  rw [eval_andList_eq_true, eval_andList_eq_true, List.forall_mem_cons]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem eval_andList_nil (x : ℕ → Bool) : (andList []).eval x = true ↔ True := by
  simp [andList, eval]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem eval_not_false (f : Fml) (x : ℕ → Bool) : (not f).eval x = true ↔ f.eval x = false := by
  simp [eval]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem eval_gtN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k + 1 < 2 ^ w) (x : ℕ → Bool) :
    (not (ltConst fs (nbits w (k + 1)))).eval x = true ↔ k < val fs x := by
  rw [eval_not_iff, eval_ltN hl hk]
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
theorem eval_geN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (not (ltConst fs (nbits w k))).eval x = true ↔ k ≤ val fs x := by
  rw [eval_not_iff, eval_ltN hl hk]
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem eval_freeTapeF {fixed : Fin 7 → Option (List Sym)} {frees : List ℕ} (hs : FreeSpec fixed frees)
    {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool) :
    (freeTapeF frees A).eval x = true ↔ FreeTape fixed (evalFields A x) := by
  rw [freeTapeF, eval_orList_eq_true]
  simp only [List.mem_map, exists_exists_and_eq_and, FreeTape]
  constructor
  · rintro ⟨j, hj, h⟩
    have hj7 := hs.lt j hj
    refine ⟨⟨j, hj7⟩, (hs.iff _).mpr hj, ?_⟩
    exact (eval_eqN hA.d (by omega) x).mp h
  · rintro ⟨j, hj, h⟩
    exact ⟨j, (hs.iff j).mp hj, (eval_eqN hA.d (by have := j.isLt; omega) x).mpr h⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem eval_tZeroF {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool) :
    (tZeroF e A).eval x = true ↔ (evalFields A x).t = 0 :=
  eval_eqN hA.t (Nat.two_pow_pos _) x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_startHeadF : (startHeadF e C).eval x = true ↔ StartHead e (evalCand C x) := by
  rw [startHeadF, eval_andList₄, eval_unitHeadF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_sign _ _ _ (eval_startCellF e G hC.A₁ x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_startStateF : (startStateF e C).eval x = true ↔ StartState e (evalCand C x) := by
  rw [startStateF, eval_andList₄, eval_unitStateF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_sign _ _ _ (eval_eqN hC.A₁.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb) x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_startFixedF (hs : TapeSpec e C.A₁ fixed tabs) :
    (startFixedF e tabs C).eval x = true ↔ StartFixed e fixed (evalCand C x) := by
  rw [startFixedF, eval_andList₄, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_orList_eq_true]
  simp only [List.mem_map, exists_exists_and_eq_and, eval_and_iff, eval_xnor_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · rintro ⟨jv, hjv, hd, hσ⟩
    obtain ⟨j, s, hj, hx, hv⟩ := hs.entry jv hjv
    refine ⟨j, s, hx, ?_, ?_⟩
    · rw [← hj]; exact (eval_eqN hC.A₁.d (by rw [hj]; have := j.isLt; omega) x).mp hd
    · show C.σ₁.eval x = _
      rw [hσ, hv]
      rfl
  · rintro ⟨j, s, hx, hd, hσ⟩
    obtain ⟨vf, hvf⟩ := hs.complete j s hx
    obtain ⟨j', s', hj, hx', hv⟩ := hs.entry _ hvf
    have hjj : j' = j := Fin.ext (by simpa using hj.symm)
    subst hjj
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    refine ⟨(j', vf), hvf, (eval_eqN hC.A₁.d (by have := j'.isLt; omega) x).mpr hd, ?_⟩
    show C.σ₁.eval x = _
    rw [hv]
    exact hσ
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_startWorkF : (startWorkF e C).eval x = true ↔ StartWork e (evalCand C x) := by
  rw [startWorkF, eval_andList₅, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_geN hC.A₁.d (by norm_num), eval_sign _ _ _ (eval_workValF e G hC.A₁ x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (tabs : List (ℕ × Fml))
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_startF (hs : TapeSpec e C.A₁ fixed tabs) :
    (startF e tabs C).eval x = true ↔ StartPred e fixed (evalCand C x) := by
  rw [startF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_startHeadF e G hC, eval_startStateF e G hC, eval_startFixedF e G fixed tabs hC x hs,
    eval_startWorkF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeBdryF : (freeBdryF e frees C).eval x = true ↔ FreeBdry e fixed (evalCand C x) := by
  rw [freeBdryF, eval_andList₆, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_bdryF e G hC.A₁, eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeOtherF : (freeOtherF e frees C).eval x = true ↔ FreeOther e fixed (evalCand C x) := by
  rw [freeOtherF, eval_andList₉, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_not_iff, eval_bdryF e G hC.A₁, eval_not_iff,
    eval_eqN hC.A₁.v (by norm_num), eval_not_iff, eval_eqN hC.A₁.v (by norm_num), eval_not_iff,
    eval_eqN hC.A₁.v (by norm_num), eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeTwoF : (freeTwoF e frees C).eval x = true ↔ FreeTwo e fixed (evalCand C x) := by
  rw [freeTwoF, eval_andList₆, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_freeTapeF e G hs hC.A₁, eval_eqN hC.A₁.p (by have := twoS5_lt e; omega),
    eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeOneOfF : (freeOneOfF e frees C).eval x = true ↔ FreeOneOf e fixed (evalCand C x) := by
  simp only [freeOneOfF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_samePosF e G hC.A₁ hC.A₂,
    eval_samePosF e G hC.A₁ hC.A₃, eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_not_iff,
    eval_bdryF e G hC.A₁, eval_eqN hC.A₁.v (by norm_num), eval_eqN hC.A₂.v (by norm_num),
    eval_eqN hC.A₃.v (by norm_num)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeNandF : (freeNandF e frees C).eval x = true ↔ FreeNand e fixed (evalCand C x) := by
  simp only [freeNandF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_samePosF e G hC.A₁ hC.A₂,
    eval_cellEqF e G hC.A₂ hC.A₃, eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_not_iff,
    eval_bdryF e G hC.A₁, eval_not_iff, eval_eqF hC.A₁.v hC.A₂.v, eval_not_false, eval_not_false,
    eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeBlankF : (freeBlankF e frees C).eval x = true ↔ FreeBlank e fixed (evalCand C x) := by
  simp only [freeBlankF, eval_andList_cons, eval_andList_nil, and_true]
  rw [eval_isCellF e G hC.A₁, eval_isCellF e G hC.A₂, eval_isCellF e G hC.A₃, eval_cellEqF e G hC.A₂ hC.A₃,
    eval_tZeroF e G hC.A₁, eval_freeTapeF e G hs hC.A₁, eval_eqF hC.A₂.t hC.A₁.t, eval_eqF hC.A₂.d hC.A₁.d,
    eval_gtN hC.A₁.p (by have := twoS5_lt e; omega), eval_not_iff, eval_bdryF e G hC.A₂,
    eval_ltF hC.A₁.p hC.A₂.p, eval_eqN hC.A₁.v (by norm_num), eval_eqN hC.A₂.v (by norm_num), eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable (fixed : Fin 7 → Option (List Sym)) (frees : List ℕ)
variable (hs : FreeSpec fixed frees) {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hs hC
theorem eval_freeF : (freeF e frees C).eval x = true ↔ FreePred e fixed (evalCand C x) := by
  rw [freeF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_freeBdryF e G fixed frees hs hC, eval_freeOtherF e G fixed frees hs hC,
    eval_freeTwoF e G fixed frees hs hC, eval_freeOneOfF e G fixed frees hs hC,
    eval_freeNandF e G fixed frees hs hC, eval_freeBlankF e G fixed frees hs hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_bdryCellF : (bdryCellF e C).eval x = true ↔ BdryCell e (evalCand C x) := by
  rw [bdryCellF, eval_andList₄, eval_unitCellF e G hC, eval_sameSignsF, eval_bdryF e G hC.A₁,
    eval_sign _ _ _ (eval_eqN hC.A₁.v (by norm_num) x)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_bdryHeadF : (bdryHeadF e C).eval x = true ↔ BdryHead e (evalCand C x) := by
  rw [bdryHeadF, eval_andList₄, eval_unitHeadF e G hC, eval_sameSignsF, eval_bdryF e G hC.A₁, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_bdryPredF : (bdryPredF e C).eval x = true ↔ BdryPred e (evalCand C x) := by
  rw [bdryPredF, eval_or_iff, eval_bdryCellF e G hC, eval_bdryHeadF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitZeroF : (emitZeroF e C).eval x = true ↔ EmitZero e (evalCand C x) := by
  rw [emitZeroF, eval_andList₄, eval_unitEmittedF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitStepF : (emitStepF e C).eval x = true ↔ EmitStep e (evalCand C x) := by
  rw [emitStepF, eval_andList₈, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmitOneF e G hC.A₃,
    eval_addN hC.A₃.t hC.A₁.t (by have := twoS5_lt e; omega), eval_eqF hC.A₂.t hC.A₃.t, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitMonoF : (emitMonoF e C).eval x = true ↔ EmitMono e (evalCand C x) := by
  rw [emitMonoF, eval_andList₉, eval_isEmittedF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_ltN hC.A₁.t (S_lt_two_pow e), eval_addN hC.A₁.t hC.A₂.t (by have := twoS5_lt e; omega),
    eval_eqF hC.A₃.t hC.A₂.t, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitOneF : (emitOneF e C).eval x = true ↔ EmitOne e (evalCand C x) := by
  rw [emitOneF, eval_andList₈, eval_isEmitOneF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_addN hC.A₁.t hC.A₂.t (by have := twoS5_lt e; omega), eval_eqF hC.A₃.t hC.A₂.t, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitOnceF : (emitOnceF e C).eval x = true ↔ EmitOnce e (evalCand C x) := by
  rw [emitOnceF, eval_andList₈, eval_isEmitOneF e G hC.A₁, eval_isEmittedF e G hC.A₂, eval_isEmittedF e G hC.A₃,
    eval_eqF hC.A₂.t hC.A₁.t, eval_eqF hC.A₃.t hC.A₂.t, eval_not_false, eval_not_false, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitBadF : (emitBadF e C).eval x = true ↔ EmitBad e (evalCand C x) := by
  rw [emitBadF, eval_andList₃, eval_unitEmitBadF e G hC, eval_sameSignsF, eval_not_false]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_emitPredF : (emitPredF e C).eval x = true ↔ EmitPred e (evalCand C x) := by
  rw [emitPredF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_emitZeroF e G hC, eval_emitStepF e G hC, eval_emitMonoF e G hC, eval_emitOneF e G hC,
    eval_emitOnceF e G hC, eval_emitBadF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_finalStateF : (finalStateF e C).eval x = true ↔ FinalState e (evalCand C x) := by
  rw [finalStateF, eval_andList₅, eval_unitStateF e G hC, eval_sameSignsF, eval_eqN hC.A₁.t (S_lt_two_pow e),
    eval_eqN hC.A₁.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_finalEmittedF : (finalEmittedF e C).eval x = true ↔ FinalEmitted e (evalCand C x) := by
  rw [finalEmittedF, eval_andList₄, eval_unitEmittedF e G hC, eval_sameSignsF, eval_eqN hC.A₁.t (S_lt_two_pow e)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_finalPredF : (finalPredF e C).eval x = true ↔ FinalPred e (evalCand C x) := by
  rw [finalPredF, eval_or_iff, eval_finalStateF e G hC, eval_finalEmittedF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem eval_mainF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)} {frees : List ℕ}
    {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (ht : TapeSpec e C.A₁ fixed tabs)
    (hf : FreeSpec fixed frees) :
    (mainF e tabs frees C).eval x = true ↔ MainPred e fixed (evalCand C x) := by
  rw [mainF, eval_orList_eq_true]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [eval_startF e G fixed tabs hC x ht, eval_freeF e G fixed frees hf hC, eval_bdryPredF e G hC,
    eval_emitPredF e G hC, eval_finalPredF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem eval_selectF (hot : List Bool) (fs : List Fml) (x : ℕ → Bool) :
    (selectF hot fs).eval x = true ↔
      ∃ i, ∃ h : i < (List.zipWith (fun b f => and (const b) f) hot fs).length,
        hot[i]'(List.lt_length_left_of_zipWith h) = true ∧
          (fs[i]'(List.lt_length_right_of_zipWith h)).eval x = true := by
  rw [selectF, eval_orList_eq_true]
  constructor
  · rintro ⟨f, hf, h⟩
    rw [List.mem_iff_getElem] at hf
    obtain ⟨i, hi, rfl⟩ := hf
    rw [List.getElem_zipWith, eval_and_iff] at h
    exact ⟨i, hi, by simpa [eval] using h.1, h.2⟩
  · rintro ⟨i, hi, hb, hf⟩
    refine ⟨_, List.getElem_mem hi, ?_⟩
    rw [List.getElem_zipWith, eval_and_iff]
    exact ⟨by simp [eval, hb], hf⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem eval_selectF_none (n : ℕ) (fs : List Fml) (x : ℕ → Bool) :
    (selectF (List.replicate n false) fs).eval x = false := by
  rw [← Bool.not_eq_true, eval_selectF]
  rintro ⟨i, hi, hb, -⟩
  rw [List.getElem_replicate] at hb
  cases hb
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
omit hFa hA in
theorem eval_winMatchN_bad : (winMatchN e Fa A badDesc).eval x = false := by
  rw [winMatchN, badDesc]
  exact eval_selectF_none 8 _ x
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem eval_auxMatchN (u : ℕ) (hu : u < G) :
    (auxMatchN e G Fa A (nbits (Gb G) u)).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.aux u) (evalFields A x) := by
  simp only [auxMatchN, SpecMatch, eval_andList_eq_true, List.mem_append, List.mem_cons, List.mem_ofFn,
    List.not_mem_nil, or_false, evalFields]
  constructor
  · intro h
    refine ⟨(eval_isAuxF e G hA x).mp (h _ (Or.inl (Or.inl rfl))),
      (eval_eqF hA.t hFa.t x).mp (h _ (Or.inl (Or.inr (Or.inl rfl)))),
      fun k => (eval_eqF (hA.js k) (hFa.js k) x).mp (h _ (Or.inr ⟨k, rfl⟩)),
      (eval_eqN hA.g (lt_trans hu (G_lt_two_pow_Gb G)) x).mp (h _ (Or.inl (Or.inr (Or.inr rfl))))⟩
  · rintro ⟨h1, h2, h3, h4⟩ f hf
    rcases hf with (rfl | rfl | rfl) | ⟨k, rfl⟩
    · exact (eval_isAuxF e G hA x).mpr h1
    · exact (eval_eqF hA.t hFa.t x).mpr h2
    · exact (eval_eqN hA.g (lt_trans hu (G_lt_two_pow_Gb G)) x).mpr h4
    · exact (eval_eqF (hA.js k) (hFa.js k) x).mpr (h3 k)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem eval_specMatchN_aux (u : ℕ) (hu : u < G) :
    (specMatchN e G Fa A (LitSpec.toN G (.aux u))).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.aux u) (evalFields A x) := by
  rw [LitSpec.toN, specMatchN, eval_mux]
  simp only [eval, if_true]
  exact eval_auxMatchN e G hFa hA x u hu
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
omit hFa hA in
theorem wvDescs_getD (n : ℕ) :
    wvDescs.getD n badDesc =
      if h : n < winCard 7 6 Sym Ctl then wvDesc ((Fintype.equivFin _).symm ⟨n, h⟩) else badDesc := by
  rw [wvDescs, List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by rw [List.length_finRange]; exact h), List.getElem_finRange]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_finRange]; omega)]
    rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem eval_specMatchN_win (n : ℕ) :
    (specMatchN e G Fa A (LitSpec.toN G (.win n))).eval x = true ↔
      SpecMatch e G (evalFields Fa x) (.win n) (evalFields A x) := by
  rw [LitSpec.toN, specMatchN, eval_mux]
  simp only [eval, Bool.false_eq_true, if_false]
  rw [wvDescs_getD, SpecMatch]
  by_cases h : n < winCard 7 6 Sym Ctl
  · rw [dif_pos h, eval_winMatchN e G hFa hA]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩
  · rw [dif_neg h, eval_winMatchN_bad]
    simp [h]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem eval_specMatchN (sp : LitSpec) (hsp : ∀ u, sp = .aux u → u < G) :
    (specMatchN e G Fa A (LitSpec.toN G sp)).eval x = true ↔
      SpecMatch e G (evalFields Fa x) sp (evalFields A x) := by
  cases sp with
  | aux u => exact eval_specMatchN_aux e G hFa hA x u (hsp u rfl)
  | win n => exact eval_specMatchN_win e G hFa hA x n
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_tplN (tp : Tpl) (hsp : ∀ sp, (sp = tp.1.1 ∨ sp = tp.2.1.1 ∨ sp = tp.2.2.1) → ∀ u, sp = .aux u → u < G) :
    (tplN e G (Tpl.toN G tp) C).eval x = true ↔ TplMatch e G tp (evalCand C x) := by
  rw [tplN, Tpl.toN, TplMatch, eval_andList₆, eval_specMatchN e G hC.A₃ hC.A₁ x _ (hsp _ (Or.inl rfl)),
    eval_specMatchN e G hC.A₃ hC.A₂ x _ (hsp _ (Or.inr (Or.inl rfl))),
    eval_specMatchN e G hC.A₃ hC.A₃ x _ (hsp _ (Or.inr (Or.inr rfl))), eval_signConst, eval_signConst,
    eval_signConst]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
omit hC in
theorem mem_tplsFrom (gs : List Gate) : ∀ (g₀ : ℕ) (l : List NTpl), l ∈ tplsFrom G g₀ gs ↔
    ∃ i, ∃ h : i < gs.length, l = (gateTemplates (g₀ + i) gs[i]).map (Tpl.toN G) := by
  induction gs with
  | nil => intro g₀ l; simp [tplsFrom]
  | cons gate gs ih =>
    intro g₀ l
    rw [tplsFrom, List.mem_cons, ih (g₀ + 1)]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨i + 1, by simp; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩
    · rintro ⟨i, hi, rfl⟩
      cases i with
      | zero => exact Or.inl (by simp)
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_windowGatesN (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt) (hin : chk.InputsLt)
    (hinp : chk.inputs = winCard 7 6 Sym Ctl) :
    (windowGatesN e G (tplsOf G chk) C).eval x = true ↔ WindowGates e G chk (evalCand C x) := by
  subst hG
  rw [windowGatesN, eval_orList_eq_true, WindowGates, tplsOf]
  simp only [List.mem_map, mem_tplsFrom, Nat.zero_add]
  constructor
  · rintro ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, h⟩
    rw [eval_orList_eq_true] at h
    obtain ⟨_, htp, h⟩ := h
    rw [List.mem_map] at htp
    obtain ⟨_, htp, rfl⟩ := htp
    rw [List.mem_map] at htp
    obtain ⟨tp, htp, rfl⟩ := htp
    refine ⟨⟨i, hi⟩, tp, htp, (eval_tplN e _ hC x tp ?_).mp h⟩
    intro sp hsp u hu
    rcases spec_lt chk hC' hin hinp ⟨i, hi⟩ tp htp sp hsp with ⟨u', hu', hlt⟩ | ⟨i', hi', -⟩
    · rw [hu] at hu'; cases hu'; exact hlt
    · rw [hu] at hi'; cases hi'
  · rintro ⟨g, tp, htp, h⟩
    refine ⟨_, ⟨_, ⟨g, g.isLt, rfl⟩, rfl⟩, ?_⟩
    rw [eval_orList_eq_true]
    refine ⟨_, List.mem_map_of_mem (List.mem_map_of_mem htp), (eval_tplN e _ hC x tp ?_).mpr h⟩
    intro sp hsp u hu
    rcases spec_lt chk hC' hin hinp g tp htp sp hsp with ⟨u', hu', hlt⟩ | ⟨i', hi', -⟩
    · rw [hu] at hu'; cases hu'; exact hlt
    · rw [hu] at hi'; cases hi'
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_windowOutF : (windowOutF e G C).eval x = true ↔ WindowOut e G (evalCand C x) := by
  rw [windowOutF, eval_andList₄, eval_unitAuxF e G hC, eval_sameSignsF,
    eval_eqN hC.A₁.g (lt_of_le_of_lt (Nat.sub_le G 1) (G_lt_two_pow_Gb G))]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool)
include hC
theorem eval_windowN (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt) (hin : chk.InputsLt)
    (hinp : chk.inputs = winCard 7 6 Sym Ctl) :
    (windowN e G (tplsOf G chk) C).eval x = true ↔ WindowPred e G chk (evalCand C x) := by
  rw [windowN, eval_or_iff, eval_windowGatesN e G hC x chk hG hC' hin hinp, eval_windowOutF e G hC]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
/-- **The tableau formula is exact**: it accepts a candidate iff the candidate decodes to a
clause of `tableau U 0 1 S fixed chk`. -/
theorem eval_tableauF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)} {frees : List ℕ}
    {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (ht : TapeSpec e C.A₁ fixed tabs)
    (hf : FreeSpec fixed frees) (chk : Circuit) (hG : G = chk.gates.length) (hC' : chk.RefsLt)
    (hin : chk.InputsLt) (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ []) :
    (tableauF e G tabs frees (tplsOf G chk) C).eval x = true ↔
      ∃ cl ∈ tableau U Sym.zero Sym.one (Sof e) fixed chk, (evalCand C x).Dec e chk.gates.length cl := by
  rw [tableauF, eval_or_iff, eval_mainF e G hC x ht hf, eval_windowN e G hC x chk hG hC' hin hinp]
  subst hG
  exact tableau_dec_iff e fixed chk hC' hin hinp hne _
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_spec : chk.WellFormed ∧ chk.inputs = winCard 7 6 Sym Ctl ∧
    chk.size ≤ 7 * 2 ^ winCard 7 6 Sym Ctl ∧
    ∀ x : Fin (winCard 7 6 Sym Ctl) → Bool, chk.evalBits (List.ofFn x) = chkFun x :=
  (Fml.exists_circuit (winCard 7 6 Sym Ctl) chkFun).choose_spec
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_wellFormed : chk.WellFormed := chk_spec.1
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_inputs : chk.inputs = winCard 7 6 Sym Ctl := chk_spec.2.1
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_refsLt : chk.RefsLt := chk_wellFormed.refsLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_inputsLt : chk.InputsLt := chk_wellFormed.inputsLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem chk_gates_ne : chk.gates ≠ [] := chk_wellFormed.nonempty
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T : ℕ)
theorem ansEnd_iff (c : Cand) :
    AnsEnd e T c ↔ ∃ cl ∈ ansEndClauses e G T, c.Dec e G cl := by
  constructor
  · rintro ⟨hu, hss, ht, hd, hp, hv, hs⟩
    obtain ⟨t, d, p, v, hdec⟩ := exists_cell e G hu.1
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ t d p v).mp hdec
    have ht0 : t = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    subst ht0
    obtain ⟨j, rfl⟩ := (tapeCode_lt_seven_iff d).mp (by rw [← hdd]; omega)
    have hvb : v = .blank := symCode_inj.mp (by rw [← hvv, hv]; rfl)
    subst hvb
    refine ⟨_, ⟨j, p, ?_, ?_, rfl⟩, (dec_unit_cell e G c _ _ _ _ _).mpr ⟨hdec, hu, hs, hss⟩⟩
    · rw [tapeCode_inl] at hdd; omega
    · omega
  · rintro ⟨_, ⟨j, p, hj, hp, rfl⟩, hdec⟩
    obtain ⟨hdec', hu, hs, hss⟩ := (dec_unit_cell e G c _ _ _ _ _).mp hdec
    obtain ⟨-, htt, hdd, hpp, hvv⟩ := (decodeVar_cell_iff e G _ _ _ p .blank).mp hdec'
    refine ⟨hu, hss, by rw [htt, Fin.val_zero], ?_, by rw [hpp, hp], by rw [hvv]; rfl, hs⟩
    rw [hdd, tapeCode_inl]
    exact hj
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T : ℕ)
theorem eval_ansEndF {C : CandF} (hC : C.Lengths e G) (x : ℕ → Bool) (hT : T + 3 < 2 ^ W e) :
    (ansEndF e T C).eval x = true ↔ AnsEnd e T (evalCand C x) := by
  rw [ansEndF, eval_andList₇, eval_unitCellF e G hC, eval_sameSignsF, eval_tZeroF e G hC.A₁,
    eval_or_iff, eval_eqN hC.A₁.d (by norm_num), eval_eqN hC.A₁.d (by norm_num),
    eval_eqN hC.A₁.p hT, eval_eqN hC.A₁.v (by norm_num)]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T : ℕ)
/-- **The describer's formula is exact**: it accepts a candidate iff the candidate decodes to
a clause of `tableauPlus`. -/
theorem eval_tableauPlusF {fixed : Fin 7 → Option (List Sym)} {tabs : List (ℕ × Fml)}
    {frees : List ℕ} {C : CandF} (hC : C.Lengths e chk.gates.length) (x : ℕ → Bool)
    (ht : TapeSpec e C.A₁ fixed tabs) (hf : FreeSpec fixed frees) (hT : T + 3 < 2 ^ W e) :
    (tableauPlusF e chk.gates.length T tabs frees (tplsOf chk.gates.length chk) C).eval x = true ↔
      ∃ cl ∈ tableauPlus e T fixed chk, (evalCand C x).Dec e chk.gates.length cl := by
  rw [tableauPlusF, eval_or_iff,
    eval_tableauF e chk.gates.length hC x ht hf chk rfl chk_refsLt chk_inputsLt chk_inputs
      chk_gates_ne,
    eval_ansEndF e chk.gates.length T hC x hT, ansEnd_iff e chk.gates.length T, tableauPlus,
    exists_mem_union]
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
theorem freeSpec (D : Prog) (n T : ℕ) (x y : BitStr) : FreeSpec (fixedOf D n T x y) [5, 6] where
  lt j hj := by simp at hj; rcases hj with rfl | rfl <;> omega
  iff j := by fin_cases j <;> simp [fixedOf]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem candOf_lengths (e G T : ℕ) : (candOf e G T).Lengths e G :=
  ⟨litFields_lengths e G T 0, litFields_lengths e G T _, litFields_lengths e G T _⟩
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
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem drop_clauseInput :
    (clauseInput (mOf e Gc) c).drop (3 * mOf e Gc) = [c.l₁.pos, c.l₂.pos, c.l₃.pos] := by
  have h3 : 3 * mOf e Gc = mOf e Gc + (mOf e Gc + mOf e Gc) := by omega
  rw [h3, ← List.drop_drop, ← List.drop_drop, clauseInput_eq,
    List.drop_left' (by rw [length_bitsOfNat]), List.drop_left' (by rw [length_bitsOfNat]),
    List.drop_left' (by rw [length_bitsOfNat])]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem getD_clauseInput_sign0 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc) false = c.l₁.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 0
  rw [drop_clauseInput] at h
  simpa using h.symm
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem getD_clauseInput_sign1 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc + 1) false = c.l₂.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 1
  rw [drop_clauseInput] at h
  simpa using h.symm
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
theorem getD_clauseInput_sign2 :
    (clauseInput (mOf e Gc) c).getD (3 * mOf e Gc + 2) false = c.l₃.pos := by
  have h := getD_drop_eq (clauseInput (mOf e Gc) c) (3 * mOf e Gc) 2
  rw [drop_clauseInput] at h
  simpa using h.symm
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
/-- The candidate of formulas, evaluated on the input bits of a clause, is the candidate of
the clause. -/
theorem evalCand_candOf (hT : T ≤ Sof e) :
    evalCand (candOf e Gc T) (fun i => (clauseInput (mOf e Gc) c).getD i false) =
      candOfClause e T c := by
  have hlf : ∀ b, evalFields (litFields e Gc T b) (fun i => (clauseInput (mOf e Gc) c).getD i false)
      = fieldsOf e Gc T (ibOf b (mOf e Gc) (fun i => (clauseInput (mOf e Gc) c).getD i false)) :=
    fun b => evalFields_litFields e Gc T b _ hT
  simp only [evalCand, candOf, candOfClause, hlf, ibOf_clauseInput_zero, ibOf_clauseInput_one,
    ibOf_clauseInput_two, eval, getD_clauseInput_sign0, getD_clauseInput_sign1,
    getD_clauseInput_sign2]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e T : ℕ) (c : Clause3 (Fin (2 ^ mOf e Gc)))
/-- **What the describer describes**: a clause is accepted iff its three indices decode to the
literals of a clause of `tableauPlus`. -/
theorem mem_formula3_iff (D : Prog) (n : ℕ) (x y : BitStr) (hT : T ≤ Sof e)
    (hlen : FixedLen e D n T x y) (hTm : T + 3 < 2 ^ W e) :
    c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) ↔
      ∃ cl ∈ tableauPlus e T (fixedOf D n T x y) chk, (candOfClause e T c).Dec e Gc cl := by
  have h1 : (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) c) =
      (descFml e T D n x y).eval (fun i => (clauseInput (mOf e Gc) c).getD i false) :=
    Fml.evalBits_toCircuit _ _ _
  have h2 := eval_tableauPlusF e T (candOf_lengths e Gc T)
    (fun i => (clauseInput (mOf e Gc) c).getD i false)
    (tapeSpec e T D n x y Gc (litFields_lengths e Gc T 0) hT hlen) (freeSpec D n T x y) hTm
  rw [evalCand_candOf e T c hT] at h2
  show (descCirc e T D n x y).evalBits (clauseInput (mOf e Gc) c) = true ↔ _
  rw [h1]
  exact h2
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
theorem _root_.solution (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y)
    (hTm : T + 3 < 2 ^ W e) (w : Fin (2 ^ mOf e Gc) → Bool)
    (hw : ((descCirc e T D n x y).formula3 (mOf e Gc)).Sat w) :
    (tableauPlus e T (fixedOf D n T x y) chk).Sat
      fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ := by
  intro cl hcl
  refine
    let c : Clause3 (Fin (2 ^ mOf e Gc)) :=
      ⟨⟨⟨idxOf e Gc T cl.l₁.var, idxOf_lt e Gc T hT _⟩, cl.l₁.pos⟩,
        ⟨⟨idxOf e Gc T cl.l₂.var, idxOf_lt e Gc T hT _⟩, cl.l₂.pos⟩,
        ⟨⟨idxOf e Gc T cl.l₃.var, idxOf_lt e Gc T hT _⟩, cl.l₃.pos⟩⟩
    ?_
  have hc : c ∈ (descCirc e T D n x y).formula3 (mOf e Gc) := by
    refine (mem_formula3_iff e T c D n x y hT hlen hTm).mpr ⟨cl, hcl, ?_, ?_, ?_⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
    · exact ⟨decodeVar_fieldsOf_idxOf e Gc T hT _, rfl⟩
  have key : Clause3.eval w c =
      Clause3.eval (fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩) cl := by
    simp only [Clause3.eval, Lit.eval, c]
  have hres := hw c hc
  rw [key] at hres
  exact hres
end MIPRE.TM.CookLevin.Desc
