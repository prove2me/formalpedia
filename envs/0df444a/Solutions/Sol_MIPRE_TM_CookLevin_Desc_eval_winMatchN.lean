-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.eval_winMatchN
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:48.184951+00:00
-- url     : https://prove2.me/submissions/fd1884b2-dac9-44bb-a666-3bb405e7bcfe

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FamilyFml.lean (solution of MIPRE.TM.CookLevin.Desc.eval_winMatchN);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
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
import Theorems.Thm_MIPRE_SAT_Fml_eval_addConstRel_iff
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat

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
theorem length_padBits (W : ℕ) (l : BitStr) (h : l.length ≤ W) : (padBits W l).length = W := by
  simp [padBits]; omega
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

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem symCode_lt (v : CellVal Sym) : symCode v < 7 := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> decide
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
theorem QC_lt_two_pow_Qb : QC < 2 ^ Qb := by
  rw [Qb]
  exact Nat.lt_size_self QC
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
open Interp SAT Cost Fml
theorem eval_eqN {fs : List Fml} {w k : ℕ} (hl : fs.length = w) (hk : k < 2 ^ w) (x : ℕ → Bool) :
    (eqConst fs (nbits w k)).eval x = true ↔ val fs x = k := by
  rw [eval_eqConst_iff _ _ (by rw [hl, length_nbits]), bitsVal_nbits_of_lt hk]
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
theorem eval_and_iff (f g : Fml) (x : ℕ → Bool) : (and f g).eval x = true ↔ f.eval x = true ∧ g.eval x = true := by
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
variable (e G : ℕ)
theorem twoS5_lt : 2 * Sof e + 5 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
theorem getElem_oneHot (n k i : ℕ) (h : i < (oneHot n k).length) : (oneHot n k)[i] = decide (i = k) := by
  simp [oneHot]
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
theorem eval_selectF_oneHot (n k : ℕ) (fs : List Fml) (hl : fs.length = n) (hk : k < n) (x : ℕ → Bool) :
    (selectF (oneHot n k) fs).eval x = true ↔ (fs[k]'(by omega)).eval x = true := by
  rw [eval_selectF]
  have hlen : (List.zipWith (fun b f => and (const b) f) (oneHot n k) fs).length = n := by
    simp [List.length_zipWith, hl]
  constructor
  · rintro ⟨i, hi, hb, hf⟩
    rw [getElem_oneHot, decide_eq_true_iff] at hb
    subst hb
    exact hf
  · intro hf
    exact ⟨k, by omega, by rw [getElem_oneHot]; simp, hf⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem eval_posF (d : Tape 7 6) (δ : ℕ) (hδ : δ < 8) :
    (posF e Fa A (oneHot 13 (tapeCode d)) (nbits 3 δ)).eval x = true ↔
      val A.p x = val (Fa.js ⟨tapeCode d, tapeCode_lt d⟩) x + δ := by
  have hS := twoS5_lt e
  rw [posF, eval_selectF_oneHot 13 _ _ (by simp) (tapeCode_lt d), List.getElem_map, List.getElem_ofFn]
  have hpad : (padBits (W e) (nbits 3 δ)).length = W e := length_padBits _ _ (by rw [length_nbits]; unfold W; omega)
  rw [eval_addConstRel_iff _ _ _ (by rw [hFa.js, hpad]) (by rw [hFa.js, hA.p]), bitsVal_padBits,
    bitsVal_nbits_of_lt hδ]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (e G : ℕ)
variable (e G : ℕ)
variable {Fa A : FieldsF} (hFa : Fa.Lengths e G) (hA : A.Lengths e G) (x : ℕ → Bool)
include hFa hA
theorem _root_.solution (wv : WinVar 7 6 Sym Ctl) :
    (winMatchN e Fa A (wvDesc wv)).eval x = true ↔ WinMatch e (evalFields Fa x) wv (evalFields A x) := by
  have hS := twoS5_lt e
  cases wv with
  | cellPre d δ v =>
    rw [wvDesc]
    rw [winMatchN]
    rw [eval_selectF_oneHot 8 0 _ rfl (by norm_num)]
    rw [WinMatch]
    simp only [List.getElem_cons_zero]
    rw [eval_andList₅, eval_isCellF e G hA, eval_eqF hA.t hFa.t, eval_eqN hA.d (by have := tapeCode_lt d; omega),
      eval_posF e G hFa hA x d δ (by have := δ.isLt; omega), eval_eqN hA.v (by have := symCode_lt v; omega)]
    rfl
  | headPre d δ =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 1 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₄, eval_isHeadF e G hA, eval_eqF hA.t hFa.t, eval_eqN hA.d (by have := tapeCode_lt d; omega),
      eval_posF e G hFa hA x d δ (by have := δ.isLt; omega)]
    rfl
  | cellPost d v =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 2 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₅, eval_isCellF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.d (by have := tapeCode_lt d; omega), eval_posF e G hFa hA x d 2 (by norm_num),
      eval_eqN hA.v (by have := symCode_lt v; omega)]
    rfl
  | headPost d =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 3 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₄, eval_isHeadF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.d (by have := tapeCode_lt d; omega), eval_posF e G hFa hA x d 2 (by norm_num)]
    rfl
  | statePre q =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 4 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₃, eval_isStateF e G hA, eval_eqF hA.t hFa.t,
      eval_eqN hA.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
    rfl
  | statePost q =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 5 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₃, eval_isStateF e G hA, eval_addN hFa.t hA.t (by omega),
      eval_eqN hA.q (lt_trans (qCode_lt _) QC_lt_two_pow_Qb)]
    rfl
  | emitOne =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 6 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₂, eval_isEmitOneF e G hA, eval_eqF hA.t hFa.t]
    rfl
  | emitBad =>
    rw [wvDesc, winMatchN, eval_selectF_oneHot 8 7 _ rfl (by norm_num), WinMatch]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    rw [eval_andList₂, eval_isEmitBadF e G hA, eval_eqF hA.t hFa.t]
    rfl
end MIPRE.TM.CookLevin.Desc
