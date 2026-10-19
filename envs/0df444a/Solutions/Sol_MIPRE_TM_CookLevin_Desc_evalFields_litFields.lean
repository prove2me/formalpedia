-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.evalFields_litFields
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:57.917982+00:00
-- url     : https://prove2.me/submissions/2db17bb8-b620-48c3-b5a6-25b8acda84a3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FieldFml.lean (solution of MIPRE.TM.CookLevin.Desc.evalFields_litFields);
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
import Theorems.Thm_MIPRE_SAT_Fml_val_addBits
import Theorems.Thm_MIPRE_SAT_bitsVal_lt
import Theorems.Thm_MIPRE_SAT_bitsVal_take
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
theorem bitsVal_map_not (l : BitStr) : bitsVal (l.map not) + bitsVal l + 1 = 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    rw [List.map_cons, bitsVal_cons', bitsVal_cons', List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega
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
theorem bitsVal_incBits (l : BitStr) : bitsVal (incBits l) = bitsVal l + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp only [incBits, bitsVal_cons', ih] <;> simp <;> omega
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

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_twosComp (c : BitStr) : bitsVal (twosComp c) = (2 ^ c.length - bitsVal c) % 2 ^ c.length := by
  unfold twosComp
  rw [bitsVal_take, bitsVal_incBits]
  have := bitsVal_map_not c
  have h2 := bitsVal_lt c
  congr 1
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
theorem val_cons (f : Fml) (fs : List Fml) (x : ℕ → Bool) :
    val (f :: fs) x = 2 * val fs x + (f.eval x).toNat := by
  simp only [val, bitsOf_cons]; rw [bitsVal_cons']
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_lt (fs : List Fml) (x : ℕ → Bool) : val fs x < 2 ^ fs.length := by
  have := bitsVal_lt (bitsOf fs x); rwa [length_bitsOf] at this
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
theorem bitsOf_constBits (c : BitStr) (x : ℕ → Bool) : bitsOf (constBits c) x = c := by
  simp [bitsOf, constBits, List.map_map, Function.comp_def, eval]
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
theorem val_addConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    val (addConstBits fs c) x + 2 ^ fs.length * ((addConstCarry fs c).eval x).toNat =
      val fs x + bitsVal c := by
  have := val_addBits fs c h (const false) x
  simpa [addConstBits, addConstCarry, eval] using this
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_addConstBits_mod (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool) :
    val (addConstBits fs c) x = (val fs x + bitsVal c) % 2 ^ fs.length := by
  have h1 := val_addConstBits fs c h x
  have h2 := val_lt (addConstBits fs c) x
  rw [length_addConstBits fs c h] at h2
  cases hc : (addConstCarry fs c).eval x
  · have h1' : val (addConstBits fs c) x = val fs x + bitsVal c := by
      rw [hc] at h1; simpa using h1
    rw [← h1', Nat.mod_eq_of_lt h2]
  · have h1' : val (addConstBits fs c) x + 2 ^ fs.length = val fs x + bitsVal c := by
      rw [hc] at h1; simpa using h1
    rw [← h1', Nat.add_mod_right, Nat.mod_eq_of_lt h2]
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

namespace MIPRE.SAT.Fml
section
open Cost
theorem val_subConstBits (fs : List Fml) (c : BitStr) (h : fs.length = c.length) (x : ℕ → Bool)
    (hc : bitsVal c ≤ val fs x) : val (subConstBits fs c) x = val fs x - bitsVal c := by
  rw [subConstBits, val_addConstBits_mod fs _ (by rw [length_twosComp]; exact h), bitsVal_twosComp, ← h]
  have hv := val_lt fs x
  have hc' := bitsVal_lt c
  rw [← h] at hc'
  have hpos : 0 < 2 ^ fs.length := Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos (bitsVal c) with h0 | h0
  · rw [h0]; simp [Nat.mod_eq_of_lt hv]
  · rw [Nat.mod_eq_of_lt (show 2 ^ fs.length - bitsVal c < 2 ^ fs.length by omega)]
    rw [show val fs x + (2 ^ fs.length - bitsVal c) = (val fs x - bitsVal c) + 2 ^ fs.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem flagOff_eq (e G : ℕ) : flagOff e G = mOf e G - 1 := by unfold flagOff mOf; omega
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
open SAT Cost Fml
theorem range'_drop_take (s n off w : ℕ) (h : off + w ≤ n) :
    ((List.range' s n).drop off).take w = List.range' (s + off) w := by
  have h1 : List.range' s n = List.range' s off ++ List.range' (s + off) (n - off) := by
    rw [List.range'_append_1, Nat.add_sub_cancel' (by omega)]
  have h2 : List.range' (s + off) (n - off) = List.range' (s + off) w ++ List.range' (s + off + w) (n - off - w) := by
    rw [List.range'_append_1, Nat.add_sub_cancel' (by omega)]
  rw [h1, List.drop_left' (by simp), h2, List.take_left' (by simp)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem bitsOf_field_ibOf (b m off w : ℕ) (h : off + w ≤ m) (x : ℕ → Bool) :
    bitsOf (field (b + off) w) x = ((ibOf b m x).drop off).take w := by
  rw [bitsOf_field, ibOf, ← List.map_drop, ← List.map_take, range'_drop_take _ _ _ _ h]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem val_field_ibOf (b m off w : ℕ) (h : off + w ≤ m) (x : ℕ → Bool) :
    val (field (b + off) w) x = bitField (ibOf b m x) off w := by
  rw [val, bitsOf_field_ibOf b m off w h]; rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem getD_ibOf (b m i : ℕ) (h : i < m) (x : ℕ → Bool) : (ibOf b m x).getD i false = x (b + i) := by
  rw [ibOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' (by simpa using h)]
  simp
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
theorem bitsOf_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) (x : ℕ → Bool) :
    bitsOf (muxList s as bs) x = if s.eval x then bitsOf as x else bitsOf bs x := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => simp [muxList]
    | cons _ _ => simp at h
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [muxList, List.zipWith_cons_cons, bitsOf_cons, eval_mux]
      rw [show List.zipWith (mux s) as bs = muxList s as bs from rfl, ih bs h]
      split <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem val_muxList (s : Fml) (as bs : List Fml) (h : as.length = bs.length) (x : ℕ → Bool) :
    val (muxList s as bs) x = if s.eval x then val as x else val bs x := by
  rw [val, bitsOf_muxList s as bs h]; split <;> rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem val_cst (w c : ℕ) (x : ℕ → Bool) : val (cst w c) x = c % 2 ^ w := by
  rw [val, cst, bitsOf_constBits, bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem val_take (fs : List Fml) (w : ℕ) (x : ℕ → Bool) : val (fs.take w) x = val fs x % 2 ^ w := by
  rw [val, val, bitsOf, bitsOf, List.map_take, bitsVal_take]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
theorem val_tail (fs : List Fml) (x : ℕ → Bool) : val fs.tail x = val fs x / 2 := by
  cases fs with
  | nil => simp [val, bitsVal_nil]
  | cons f fs => rw [List.tail_cons, val_cons]; cases f.eval x <;> simp <;> omega
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
theorem eval_flagF : (flagF e G b).eval x = (ibOf b (mOf e G) x).getD (flagOff e G) false := by
  rw [getD_ibOf _ _ _ (by rw [flagOff_eq]; unfold mOf; omega)]; rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem val_jF : val (jF e G b) x = bitField (ibOf b (mOf e G) x) 0 (flagOff e G) := by
  have := val_field_ibOf b (mOf e G) 0 (flagOff e G) (by rw [flagOff_eq]; unfold mOf; omega) x
  rw [Nat.add_zero] at this
  exact this
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
/-- The answer bound: `4T < 2^{m-1}`, from `T ≤ S`. -/
theorem fourT_lt (hT : T ≤ Sof e) : 4 * T < 2 ^ flagOff e G := by
  have h1 : 2 ^ (e + 2) ≤ 2 ^ flagOff e G := Nat.pow_le_pow_right (by omega) (by unfold flagOff W; omega)
  have : 4 * T ≤ 2 ^ (e + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ]; unfold Sof at hT; omega
  have h2 : 2 ^ (e + 2) < 2 ^ flagOff e G := Nat.pow_lt_pow_right (by omega) (by unfold flagOff W; omega)
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem eval_lt2TF (hT : T ≤ Sof e) :
    (lt2TF e G T b).eval x = true ↔ bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T := by
  rw [lt2TF, eval_ltConst_iff _ _ (by rw [length_jF, twoTb, length_nbits]), val_jF, twoTb,
    bitsVal_nbits_of_lt (by have := fourT_lt e G T hT; omega)]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem val_rF (hT : T ≤ Sof e) :
    val (rF e G T b) x =
      if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
      else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T := by
  rw [rF, val_muxList _ _ _ (by rw [length_jF, length_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]), length_jF])]
  have h2T : bitsVal (twoTb e G T) = 2 * T := by
    rw [twoTb, bitsVal_nbits_of_lt (by have := fourT_lt e G T hT; omega)]
  by_cases hlt : bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T
  · rw [if_pos ((eval_lt2TF e G T b x hT).mpr hlt), if_pos hlt, val_jF]
  · rw [if_neg (by rw [eval_lt2TF e G T b x hT]; exact hlt), if_neg hlt,
      val_subConstBits _ _ (by rw [length_jF, twoTb, length_nbits]) x (by rw [h2T, val_jF]; omega), h2T, val_jF]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem val_pAnsF (hT : T ≤ Sof e) :
    val (pAnsF e G T b) x =
      ((if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
        else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) / 2 + 3) % 2 ^ W e := by
  have hW := W_le_flagOff e G
  have hlen : ((rF e G T b).tail.take (W e)).length = W e := by
    simp [List.length_take, length_rF]; omega
  rw [pAnsF, val_addConstBits_mod _ _ (by rw [hlen]; simp), hlen, val_take, val_tail, val_rF e G T b x hT,
    bitsVal_nbits_of_lt (by unfold W; rw [Nat.pow_succ, Nat.pow_succ]; have := Nat.one_le_two_pow (n := e + 2); omega),
    Nat.mod_add_mod]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem eval_ansOkF (hT : T ≤ Sof e) :
    (and (not (flagF e G b)) (ltConst (jF e G b) (nbits (flagOff e G) (4 * T)))).eval x =
      (!(flagF e G b).eval x && decide (bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 4 * T)) := by
  simp only [eval]
  congr 1
  rw [Bool.eq_iff_iff, eval_ltConst_iff _ _ (by simp [jF]), val_jF, bitsVal_nbits_of_lt (fourT_lt e G T hT),
    decide_eq_true_iff]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open SAT Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)
theorem _root_.solution (hT : T ≤ Sof e) :
    evalFields (litFields e G T b) x = fieldsOf e G T (ibOf b (mOf e G) x) := by
  have hm : mOf e G = flagOff e G + 1 := by rw [flagOff_eq]; unfold mOf; omega
  have hoff : ∀ off w, off + w ≤ flagOff e G →
      val (field (b + off) w) x = bitField (ibOf b (mOf e G) x) off w :=
    fun off w h => val_field_ibOf b (mOf e G) off w (by omega) x
  have hflag := eval_flagF e G b x
  have hansOk := eval_ansOkF e G T b x hT
  rw [hflag] at hansOk
  have hQ : Qb ≤ flagOff e G := by unfold flagOff; omega
  have hGb : Gb G ≤ flagOff e G := by unfold flagOff; omega
  have hjs : ∀ k : Fin 13, jsOff e k + W e ≤ flagOff e G := fun k => by
    unfold jsOff flagOff; have := k.isLt; nlinarith
  unfold evalFields litFields fieldsOf
  simp only
  cases hb : (ibOf b (mOf e G) x).getD (flagOff e G) false
  · rw [if_neg (by simp)]
    rw [hb] at hflag hansOk
    have hmux : ∀ (as bs : List Fml) (h : as.length = bs.length),
        val (muxList (flagF e G b) as bs) x = val bs x := fun as bs h => by
      rw [val_muxList _ _ _ h, hflag]; rfl
    have h_tag : val (muxList (flagF e G b) (field (b + tagOff) 3) (cst 3 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_t : val (muxList (flagF e G b) (field (b + tOff) (W e)) (cst (W e) 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_q : val (muxList (flagF e G b) (field (b + qOff e) Qb) (cst Qb 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_g : val (muxList (flagF e G b) (field (b + gOff e) (Gb G)) (cst (Gb G) 0)) x = 0 := by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_js : ∀ k : Fin 13,
        val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x = 0 := fun k => by
      rw [hmux _ _ (by simp), val_cst, Nat.zero_mod]
    have h_d : val (muxList (flagF e G b) (field (b + dOff e) 4)
        (muxList (lt2TF e G T b) (cst 4 5) (cst 4 6))) x =
        if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then 5 else 6 := by
      rw [hmux _ _ (by rw [length_dAns]; simp), val_muxList _ _ _ (by simp)]
      by_cases hlt : bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T
      · rw [if_pos ((eval_lt2TF e G T b x hT).mpr hlt), if_pos hlt, val_cst]; rfl
      · rw [if_neg (by rw [eval_lt2TF e G T b x hT]; exact hlt), if_neg hlt, val_cst]; rfl
    have h_p : val (muxList (flagF e G b) (field (b + pOff e) (W e)) (pAnsF e G T b)) x =
        ((if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) / 2 + 3) % 2 ^ W e := by
      rw [hmux _ _ (by rw [length_pAnsF]; simp), val_pAnsF e G T b x hT]
    have h_v : val (muxList (flagF e G b) (field (b + vOff e) 3)
        (muxList ((rF e G T b).headD (const false)) (cst 3 1) (cst 3 5))) x =
        if (if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) % 2 = 1 then 1 else 5 := by
      rw [hmux _ _ (by rw [length_vAns]; simp), val_muxList _ _ _ (by simp)]
      have hne : rF e G T b ≠ [] := by
        intro h; have := length_rF e G T b; rw [h] at this; simp at this; unfold flagOff at this; omega
      have hhead := headD_eval_toNat (rF e G T b) x hne
      rw [val_rF e G T b x hT] at hhead
      generalize (if bitField (ibOf b (mOf e G) x) 0 (flagOff e G) < 2 * T then
          bitField (ibOf b (mOf e G) x) 0 (flagOff e G)
          else bitField (ibOf b (mOf e G) x) 0 (flagOff e G) - 2 * T) = r at hhead ⊢
      by_cases hodd : r % 2 = 1
      · have : ((rF e G T b).headD (const false)).eval x = true := by
          cases h : ((rF e G T b).headD (const false)).eval x
          · rw [h, Bool.toNat_false] at hhead; omega
          · rfl
        rw [if_pos hodd, if_pos this, val_cst]; rfl
      · have : ((rF e G T b).headD (const false)).eval x = false := by
          cases h : ((rF e G T b).headD (const false)).eval x
          · rfl
          · rw [h, Bool.toNat_true] at hhead; omega
        rw [if_neg hodd, if_neg (by rw [this]; decide), val_cst]; rfl
    have hjsf : (fun k : Fin 13 => val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x) =
        fun _ => 0 := funext h_js
    rw [hflag, hansOk, h_tag, h_t, h_q, h_g, h_d, h_p, h_v, hjsf]
    simp only [Bool.not_false, Bool.true_and]
  · rw [if_pos (by simp)]
    rw [hb] at hflag hansOk
    have hmux : ∀ (as bs : List Fml) (h : as.length = bs.length),
        val (muxList (flagF e G b) as bs) x = val as x := fun as bs h => by
      rw [val_muxList _ _ _ h, hflag]; rfl
    have hjsf : (fun k : Fin 13 => val (muxList (flagF e G b) (field (b + jsOff e k) (W e)) (cst (W e) 0)) x) =
        fun k : Fin 13 => bitField (ibOf b (mOf e G) x) (jsOff e k) (W e) := by
      funext k; rw [hmux _ _ (by simp), hoff _ _ (hjs k)]
    rw [hflag, hansOk, hmux _ _ (by simp), hmux _ _ (by simp), hmux _ _ (by rw [length_dAns]; simp),
      hmux _ _ (by rw [length_pAnsF]; simp), hmux _ _ (by rw [length_vAns]; simp),
      hmux _ _ (by simp), hmux _ _ (by simp), hjsf,
      hoff _ _ (by unfold tagOff flagOff; omega), hoff _ _ (by unfold tOff flagOff; omega),
      hoff _ _ (by unfold dOff flagOff; omega), hoff _ _ (by unfold pOff flagOff; omega),
      hoff _ _ (by unfold vOff flagOff; omega), hoff _ _ (by unfold qOff flagOff; omega),
      hoff _ _ (by unfold gOff flagOff; omega)]
    simp only [Bool.not_true, Bool.false_and]
end MIPRE.TM.CookLevin.Desc
