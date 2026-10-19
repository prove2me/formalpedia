-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.decodeVar_encodeVar
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:02.252575+00:00
-- url     : https://prove2.me/submissions/1cd7488f-4fd3-49d5-bb68-0f15fa91ba27

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Layout.lean (solution of MIPRE.TM.CookLevin.Desc.decodeVar_encodeVar);
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
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_bitsVal_bitsOfNat

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem symCode_lt (v : CellVal Sym) : symCode v < 7 := by
  rcases v with ⟨_ | _ | _ | _ | _⟩ | _ | _ <;> decide
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem tapeOfCode_tapeCode (d : Tape 7 6) : tapeOfCode (tapeCode d) = some d := by
  rcases d with ⟨j, hj⟩ | ⟨j, hj⟩
  · simp [tapeOfCode, tapeCode, hj]
  · show tapeOfCode (7 + j) = _
    unfold tapeOfCode
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    ext
    simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem qOfCode_qCode (q : Option Ctl) : qOfCode (qCode q) = some q := by
  unfold qOfCode qCode
  rw [dif_pos (show ((Fintype.equivFin (Option Ctl)) q : ℕ) < QC from
    (by unfold QC; exact (Fintype.equivFin (Option Ctl) q).isLt))]
  congr 1
  exact (Fintype.equivFin (Option Ctl)).symm_apply_apply q
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
theorem jsPack_add (w : ℕ) (js : ℕ → ℕ) : ∀ (a n k : ℕ),
    jsPack w js a (n + k) = jsPack w js a n ++ jsPack w js (a + n) k
  | _, 0, k => by simp [jsPack]
  | a, n + 1, k => by
    rw [Nat.succ_add, jsPack, jsPack, jsPack_add w js (a + 1) n k, List.append_assoc,
      show a + 1 + n = a + (n + 1) by omega]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
/-- Reading a field out of a concatenation. -/
theorem bitField_of_eq (ib pre mid post : BitStr) (off w : ℕ) (h : ib = pre ++ (mid ++ post))
    (hoff : pre.length = off) (hw : mid.length = w) : bitField ib off w = bitsVal mid := by
  rw [bitField, h, List.drop_left' hoff, List.take_left' hw]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
theorem getD_of_eq (ib pre post : BitStr) (b : Bool) (off : ℕ) (h : ib = pre ++ (b :: post))
    (hoff : pre.length = off) : ib.getD off false = b := by
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hoff, Nat.sub_self]
  rfl
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_flag : (packFields e G tag t d p v q js g).getD (flagOff e G) false = true := by
  refine getD_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 13 ++ nbits (Gb G) g) [] true _
    (by simp only [packFields, List.append_assoc, List.singleton_append]) ?_
  simp [flagOff]; ring
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_tag : bitField (packFields e G tag t d p v q js g) tagOff 3 = tag % 2 ^ 3 := by
  rw [bitField_of_eq _ [] (nbits 3 tag) (nbits (W e) t ++ (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))))))) tagOff 3
    (by simp only [packFields, List.nil_append]) (by simp [tagOff]) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_t : bitField (packFields e G tag t d p v q js g) tOff (W e) = t % 2 ^ W e := by
  rw [bitField_of_eq _ (nbits 3 tag) (nbits (W e) t) (nbits 4 d ++ (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))))) _ _
    (by simp only [packFields]) (by simp [tOff]) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_d : bitField (packFields e G tag t d p v q js g) (dOff e) 4 = d % 2 ^ 4 := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t) (nbits 4 d) (nbits (W e) p ++ (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [dOff]) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_p : bitField (packFields e G tag t d p v q js g) (pOff e) (W e) = p % 2 ^ W e := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d) (nbits (W e) p) (nbits 3 v ++
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [pOff]; ring) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_v : bitField (packFields e G tag t d p v q js g) (vOff e) 3 = v % 2 ^ 3 := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p) (nbits 3 v)
    (nbits Qb q ++ (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true]))) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [vOff]; ring) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_q : bitField (packFields e G tag t d p v q js g) (qOff e) Qb = q % 2 ^ Qb := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v)
    (nbits Qb q) (jsPack (W e) js 0 13 ++ (nbits (Gb G) g ++ [true])) _ _
    (by simp only [packFields, List.append_assoc]) (by simp [qOff]; ring) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_js (k : ℕ) (hk : k < 13) :
    bitField (packFields e G tag t d p v q js g) (jsOff e k) (W e) = js k % 2 ^ W e := by
  have hsplit : jsPack (W e) js 0 13 =
      jsPack (W e) js 0 k ++ (nbits (W e) (js k) ++ jsPack (W e) js (k + 1) (12 - k)) := by
    rw [show 13 = k + (1 + (12 - k)) by omega, jsPack_add, jsPack_add, Nat.zero_add]
    simp [jsPack]
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 k) (nbits (W e) (js k))
    (jsPack (W e) js (k + 1) (12 - k) ++ (nbits (Gb G) g ++ [true])) _ _
    (by simp only [packFields, hsplit, List.append_assoc]) (by simp [jsOff]; ring) (by simp),
    bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
theorem packFields_g : bitField (packFields e G tag t d p v q js g) (gOff e) (Gb G) = g % 2 ^ Gb G := by
  rw [bitField_of_eq _ (nbits 3 tag ++ nbits (W e) t ++ nbits 4 d ++ nbits (W e) p ++ nbits 3 v ++
    nbits Qb q ++ jsPack (W e) js 0 13) (nbits (Gb G) g) [true] _ _
    (by simp only [packFields, List.append_assoc]) (by simp [gOff]; ring) (by simp), bitsVal_nbits]
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ) (tag t d p v q : ℕ) (js : ℕ → ℕ) (g : ℕ)
/-- The fields of a structured index are the packed values (reduced modulo their widths). -/
theorem fieldsOf_packFields (T : ℕ) :
    fieldsOf e G T (packFields e G tag t d p v q js g) =
      { flag := true, tag := tag % 2 ^ 3, t := t % 2 ^ W e, d := d % 2 ^ 4, p := p % 2 ^ W e,
        v := v % 2 ^ 3, q := q % 2 ^ Qb, js := (fun k : Fin 13 => js k % 2 ^ W e),
        g := g % 2 ^ Gb G, ansOk := false } := by
  unfold fieldsOf
  rw [if_pos (packFields_flag e G tag t d p v q js g)]
  simp only [packFields_tag, packFields_t, packFields_d, packFields_p, packFields_v, packFields_q,
    packFields_g]
  congr 1
  funext k
  exact packFields_js e G tag t d p v q js g k k.isLt
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
variable (e G : ℕ)
theorem jsFun_tapeCode (js : Tape 7 6 → Center (Sof e)) (d : Tape 7 6) : jsFun e js (tapeCode d) = js d := by
  simp [jsFun, tapeOfCode_tapeCode]
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
open Interp SAT Cost
variable (e G : ℕ)
theorem Sof_lt_two_pow_W : (Sof e) < 2 ^ W e := by
  have := numCells_lt_two_pow_W e; unfold numCells at this; omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (e G : ℕ)
theorem _root_.solution (T : ℕ) (v : TabVar 7 6 Sym Ctl (Sof e) G) :
    decodeVar e G (fieldsOf e G T (encodeVar e G v)) = some v := by
  have hW := numCells_lt_two_pow_W e
  have hS := Sof_lt_two_pow_W e
  cases v with
  | cell t d p v =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hp : (p : ℕ) % 2 ^ W e = p := Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hd : tapeCode d % 16 = tapeCode d := Nat.mod_eq_of_lt (by have := tapeCode_lt d; omega)
    have hv : symCode v % 8 = symCode v := Nat.mod_eq_of_lt (by have := symCode_lt v; omega)
    simp only [decodeVar, ht, hp, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [dif_pos ⟨by have := t.isLt; omega, p.isLt⟩, hd, hv, tapeOfCode_tapeCode, symOfCode_symCode]
  | head t d p =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hp : (p : ℕ) % 2 ^ W e = p := Nat.mod_eq_of_lt (by have := p.isLt; omega)
    have hd : tapeCode d % 16 = tapeCode d := Nat.mod_eq_of_lt (by have := tapeCode_lt d; omega)
    simp only [decodeVar, ht, hp, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    rw [dif_pos ⟨by have := t.isLt; omega, p.isLt⟩, hd, tapeOfCode_tapeCode]
  | state t q =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hq : qCode q % 2 ^ Qb = qCode q :=
      Nat.mod_eq_of_lt (lt_trans (qCode_lt q) QC_lt_two_pow_Qb)
    simp only [decodeVar, ht, hq, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte, qOfCode_qCode]
    rw [dif_pos (by have := t.isLt; omega)]
  | emitOne t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos t.isLt]
  | emitBad t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos t.isLt]
  | emitted t =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    simp only [decodeVar, ht, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, ↓reduceIte]
    rw [dif_pos (by have := t.isLt; omega)]
  | aux t js g =>
    simp only [encodeVar, fieldsOf_packFields]
    have ht : (t : ℕ) % 2 ^ W e = t := Nat.mod_eq_of_lt (by have := t.isLt; omega)
    have hg : (g : ℕ) % 2 ^ Gb G = g := Nat.mod_eq_of_lt (lt_trans g.isLt (G_lt_two_pow_Gb G))
    have hjs : ∀ k : ℕ, jsFun e js k % 2 ^ W e = jsFun e js k := by
      intro k
      apply Nat.mod_eq_of_lt
      unfold jsFun
      split
      · rename_i d _
        have := (js d).isLt
        have h1 := Nat.one_le_two_pow (n := e)
        unfold Sof at this; unfold W; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
      · exact Nat.two_pow_pos _
    simp only [decodeVar, ht, hg, hjs, Nat.zero_mod, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      ↓reduceIte]
    have hjs' : ∀ k : Fin 13, jsFun e js k < 2 * (Sof e) + 3 := fun k => by
      unfold jsFun
      split
      · rename_i d _; exact (js d).isLt
      · omega
    rw [dif_pos ⟨t.isLt, hjs', g.isLt⟩]
    congr 1
    congr 1
    funext d
    ext
    simp [jsFun_tapeCode]
end MIPRE.TM.CookLevin.Desc
