-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.eval_isAuxF
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:01.377371+00:00
-- url     : https://prove2.me/submissions/5722fbc8-8784-45d6-a47e-ef54886cd091

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Kinds.lean (solution of MIPRE.TM.CookLevin.Desc.eval_isAuxF);
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
omit hA in
theorem S_succ_lt : Sof e + 1 < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem _root_.solution : (isAuxF e G A).eval x = true ↔ IsAux e G (evalFields A x) := by
  have hS := S_succ_lt e
  have hC := numCells_lt_two_pow_W e
  have h2 : 2 * Sof e + 3 < 2 ^ W e := by unfold numCells at hC; omega
  simp only [isAuxF, IsAux, evalFields, eval_andList_eq_true, List.mem_append, List.mem_cons,
    List.mem_ofFn, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨h _ (Or.inl (Or.inl rfl)), ?_, ?_, fun k => ?_, ?_⟩
    · exact (eval_eqTag e G hA x 6 (by omega)).mp (h _ (Or.inl (Or.inr (Or.inl rfl))))
    · exact (eval_ltT e G hA x _ (by omega)).mp (h _ (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
    · have := h _ (Or.inr ⟨k, rfl⟩)
      rwa [eval_ltConst_iff _ _ (by rw [hA.js, length_nbits]), bitsVal_nbits_of_lt h2] at this
    · have := h _ (Or.inl (Or.inr (Or.inr (Or.inr rfl))))
      rwa [eval_ltConst_iff _ _ (by rw [hA.g, length_nbits]), bitsVal_nbits_of_lt (G_lt_two_pow_Gb G)] at this
  · rintro ⟨h1, h2', h3, h4, h5⟩ f hf
    rcases hf with (rfl | rfl | rfl | rfl) | ⟨k, rfl⟩
    · exact h1
    · exact (eval_eqTag e G hA x 6 (by omega)).mpr h2'
    · exact (eval_ltT e G hA x _ (by omega)).mpr h3
    · rw [eval_ltConst_iff _ _ (by rw [hA.g, length_nbits]), bitsVal_nbits_of_lt (G_lt_two_pow_Gb G)]
      exact h5
    · rw [eval_ltConst_iff _ _ (by rw [hA.js, length_nbits]), bitsVal_nbits_of_lt h2]
      exact h4 k
end MIPRE.TM.CookLevin.Desc
