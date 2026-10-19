-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.eval_cellValF
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:44.721111+00:00
-- url     : https://prove2.me/submissions/bf6d8262-25dd-476f-9da9-fb2ec920dcdb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FamilyFml.lean (solution of MIPRE.TM.CookLevin.Desc.eval_cellValF);
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
theorem eval_mux (s a b : Fml) (x : ℕ → Bool) :
    (mux s a b).eval x = if s.eval x then a.eval x else b.eval x := by
  simp only [mux, eval]; cases s.eval x <;> simp
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
variable (e G : ℕ)
theorem codesOf_lt (x : List Sym) : ∀ c ∈ codesOf x, c < 7 := by
  intro c hc
  rw [codesOf, List.mem_map] at hc
  obtain ⟨s, -, rfl⟩ := hc
  exact symCode_lt _
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
theorem eval_lookupList (codes : List ℕ) (hc : ∀ c ∈ codes, c < 8) :
    ∀ k, k + codes.length < 2 ^ W e →
      ((orList (lookupList e A k codes)).eval x = true ↔
        ∃ i, ∃ h : i < codes.length, val A.p x = k + i ∧ val A.v x = codes[i]) := by
  induction codes with
  | nil => intro k _; simp [lookupList, orList, eval]
  | cons c cs ih =>
    intro k hk
    simp only [List.length_cons] at hk
    rw [lookupList, eval_orList_eq_true]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [← eval_orList_eq_true, ih (fun c hc' => hc c (List.mem_cons_of_mem _ hc')) (k + 1) (by omega),
      eval_and_iff, eval_eqN hA.p (by omega), eval_eqN hA.v (hc c (List.mem_cons_self ..))]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨i, hi, h1, h2⟩)
      · exact ⟨0, by simp, by omega, by simpa using h2⟩
      · exact ⟨i + 1, by simp; omega, by omega, by simpa using h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      cases i with
      | zero => exact Or.inl ⟨by omega, by simpa using h2⟩
      | succ i => exact Or.inr ⟨i, by simp at hi; omega, by omega, by simpa using h2⟩
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA
theorem _root_.solution (s : List Sym) (hs : s.length ≤ Sof e) :
    (cellValF e A (codesOf s)).eval x = true ↔
      (evalFields A x).v = cellCode s (Sof e) (evalFields A x).p := by
  have hS := twoS5_lt e
  have hlen : (codesOf s).length = s.length := by simp [codesOf]
  have hp : (evalFields A x).p = val A.p x := rfl
  have hv : (evalFields A x).v = val A.v x := rfl
  rw [cellValF, eval_mux, cellCode]
  by_cases hb : Bdry (Sof e) (evalFields A x).p
  · rw [if_pos ((eval_bdryF e G hA x).mpr hb),
      if_pos (show (evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p from hb)]
    exact eval_eqN (k := 6) hA.v (by norm_num) x
  · rw [if_neg (fun h => hb ((eval_bdryF e G hA x).mp h)),
      if_neg (show ¬ ((evalFields A x).p < 2 ∨ 2 * Sof e + 5 ≤ (evalFields A x).p) from hb), eval_mux]
    have hrange : (and (not (ltConst A.p (nbits (W e) 3)))
        (ltConst A.p (nbits (W e) ((codesOf s).length + 3)))).eval x = true ↔
        3 ≤ (evalFields A x).p ∧ (evalFields A x).p - 3 < s.length := by
      rw [eval_and_iff, eval_not_iff, eval_ltN hA.p (by omega), eval_ltN hA.p (by omega)]
      omega
    by_cases hr : 3 ≤ (evalFields A x).p ∧ (evalFields A x).p - 3 < s.length
    · rw [if_pos (hrange.mpr hr), dif_pos hr,
        eval_lookupList e G hA x _ (fun c hc => by have := codesOf_lt s c hc; omega) 3 (by omega)]
      constructor
      · rintro ⟨i, hi, hpi, hvi⟩
        obtain rfl : i = (evalFields A x).p - 3 := by omega
        rw [hv, hvi]
        simp only [codesOf, List.getElem_map]
      · intro hvs
        refine ⟨(evalFields A x).p - 3, by omega, by omega, ?_⟩
        rw [← hv, hvs]
        simp only [codesOf, List.getElem_map]
    · rw [if_neg (fun h => hr (hrange.mp h)), dif_neg hr]
      exact eval_eqN (k := 5) hA.v (by norm_num) x
end MIPRE.TM.CookLevin.Desc
