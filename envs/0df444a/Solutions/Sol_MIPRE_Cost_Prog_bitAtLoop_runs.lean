-- Prove2me | solution 1 for MIPRE.Cost.Prog.bitAtLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:51:05.251073+00:00
-- url     : https://prove2.me/submissions/fe59ec36-9419-4927-859b-a15be3b96879

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BitQuery.lean (solution of MIPRE.Cost.Prog.bitAtLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Theorems.Thm_MIPRE_Cost_Prog_bitAtBody_succ
import Theorems.Thm_MIPRE_Cost_Prog_decProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_isZeroProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem size_ofBool (b : Bool) : (ofBool b).size ≤ 3 := by cases b <;> simp [ofBool]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem size_ofList_le {α : Type*} {f : α → Data} {B : ℕ} (hf : ∀ a, (f a).size ≤ B)
    (l : List α) : (ofList f l).size ≤ (B + 1) * l.length + 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a l ih =>
    have := hf a
    simp only [ofList, size_cons, List.length_cons, Nat.mul_succ]
    omega
end MIPRE.Cost.Data

namespace MIPRE.Cost
theorem esize_bitStr_le (x : BitStr) : esize x ≤ 4 * x.length + 1 :=
  Data.size_ofList_le Data.size_ofBool x
end MIPRE.Cost

namespace MIPRE.Cost.Prog
theorem revOntoBody_wellScoped : revOntoBody.WellScoped 1 := by
  simp [revOntoBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem revOntoProg_wellScoped : revOntoProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, revOntoBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost
theorem bitsVal_eq_zero_iff (l : BitStr) : bitsVal l = 0 ↔ l.any id = false := by
  induction l with
  | nil => simp
  | cons b l ih =>
    cases b <;> simp [Nat.bit_val, ih]
end MIPRE.Cost

namespace MIPRE.Cost
theorem bitsVal_replicate_true_append (j : ℕ) (rest : BitStr) :
    bitsVal (List.replicate j true ++ false :: rest) + 1 =
      bitsVal (List.replicate j false ++ true :: rest) := by
  induction j with
  | zero => simp [Nat.bit_val]
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, bitsVal_cons, Nat.bit_val,
      Bool.toNat_false, Bool.toNat_true]
    omega
end MIPRE.Cost

namespace MIPRE.Cost
/-- A bit string with a `true` bit splits as `false^j ++ true :: rest`. -/
theorem exists_split_of_any (l : BitStr) (h : l.any id = true) :
    ∃ j rest, l = List.replicate j false ++ true :: rest := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    cases b with
    | true => exact ⟨0, l, rfl⟩
    | false =>
      simp only [List.any_cons, id, Bool.false_or] at h
      obtain ⟨j, rest, rfl⟩ := ih h
      exact ⟨j + 1, rest, by simp [List.replicate_succ]⟩
end MIPRE.Cost

namespace MIPRE.Cost.Prog
theorem isZeroBody_wellScoped : isZeroBody.WellScoped 1 := by
  simp [isZeroBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroProg_wellScoped : isZeroProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, isZeroBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroProg_runs' (mb : BitStr) (env : Env) :
    ∃ t ≤ zeroBound mb.length, Eval (encode mb :: env) isZeroProg (encode (mb.any id)) t :=
  isZeroProg_runs mb env (4 * mb.length + 1) (esize_bitStr_le mb)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decProg_runs' (mb : BitStr) (h : mb.any id = true) :
    ∃ mb' t, t ≤ decBound mb.length ∧ mb'.length = mb.length ∧ bitsVal mb' + 1 = bitsVal mb ∧
      decProg.Runs (encode mb) (encode mb') t := by
  obtain ⟨j, rest, rfl⟩ := exists_split_of_any mb h
  obtain ⟨t, ht, hrun⟩ := decProg_runs j rest
  refine ⟨List.replicate j true ++ false :: rest, t, ?_, by simp,
    bitsVal_replicate_true_append j rest, hrun⟩
  have hlen : (List.replicate j false ++ true :: rest).length = j + 1 + rest.length := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hsr : (encode rest).size ≤ 4 * rest.length + 1 := esize_bitStr_le rest
  rw [hlen]
  unfold decBound
  calc t ≤ (j + 2) * (10 * (2 * j + (encode rest).size + 4) + 60) := ht
    _ ≤ (j + 1 + rest.length + 2) * (10 * (6 * (j + 1 + rest.length) + 4) + 60) :=
        Nat.mul_le_mul (by omega) (by omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem bitAtBody_wellScoped : bitAtBody.WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, ⟨trivial, trivial⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) isZeroProg_wellScoped, ?_⟩
  refine ⟨by decide, ⟨trivial, by simp [WellScoped]⟩, ⟨trivial, trivial⟩,
    ⟨by simp [WellScoped], ?_⟩⟩
  exact callVar_wellScoped (by decide) decProg_wellScoped
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- The body on an exhausted string: stop with the out-of-range marker. -/
theorem bitAtBody_nil (mb : BitStr) :
    Eval [.cons (encode ([] : BitStr)) (encode mb)] bitAtBody (.cons .nil (.ofNat 2)) 9 := by
  have e := Eval.elim_cons (env := [Data.cons (encode ([] : BitStr)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode ([] : BitStr)) (b := encode mb) (by simp)
    (Eval.elim_nil (i := 0)
      (c := .let_ (callVar 3 isZeroProg)
        (.elim 0 (.cons .nil (.var 1))
          (.cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))))) (by simp)
      (Eval.cons (Eval.nil _) (Eval.const _ (.ofNat 2))))
  exact e.cast_cost (by simp [Data.size_ofNat])
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- The body when the index is zero: stop with the head bit. -/
theorem bitAtBody_zero (b : Bool) (ys mb : BitStr) (hz : mb.any id = false) (tz : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody (.cons .nil (encode b))
      ((encode mb).size + tz + (encode b).size + 9) := by
  rw [hz] at hzr
  have e := Eval.elim_cons (env := [Data.cons (encode (b :: ys)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode (b :: ys)) (b := encode mb) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.const (.ofNat 2))) (a := encode b)
      (b := encode ys) (by simp)
      (Eval.let_ (callVar_eval (i := 3) isZeroProg_wellScoped (v := encode mb) (by simp) hzr)
        (Eval.elim_nil (i := 0)
          (c := .cons (.cons .nil .nil) (.cons (.var 4) (callVar 6 decProg))) (by simp)
          (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encode b) (by simp))))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (m : ℕ) (y mb : BitStr) (hmb : bitsVal mb = m) (env : Env) (sy L : ℕ)
    (hsy : (encode y).size ≤ sy) (hL : mb.length = L) :
    ∃ t ≤ (y.length + 1) * bitAtIter sy L,
      Eval (.cons (encode y) (encode mb) :: env) bitAtProg (bitQueryAnswer y m) t := by
  have hI : bitAtIter sy L = sy + 8 * L + zeroBound L + decBound L + 20 := rfl
  have hmbsize : (encode mb).size ≤ 4 * L + 1 := by
    rw [← hL]; exact esize_bitStr_le mb
  induction m generalizing y mb with
  | zero =>
    have hz : mb.any id = false := (bitsVal_eq_zero_iff mb).1 hmb
    rcases y with _ | ⟨b, ys⟩
    · refine ⟨9 + 1, ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_nil mb) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
    · obtain ⟨tz, htz, hzr⟩ := isZeroProg_runs' mb []
      have hb : (encode b).size ≤ 3 := Data.size_ofBool b
      refine ⟨(encode mb).size + tz + (encode b).size + 9 + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        have h1 : bitAtIter sy L ≤ (ys.length + 1 + 1) * bitAtIter sy L :=
          Nat.le_mul_of_pos_left _ (by omega)
        rw [hL] at htz
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_zero b ys mb hz tz hzr) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
  | succ m ih =>
    have hz : mb.any id = true := by
      cases h : mb.any id with
      | false =>
        have := (bitsVal_eq_zero_iff mb).2 h
        omega
      | true => rfl
    rcases y with _ | ⟨b, ys⟩
    · refine ⟨9 + 1, ?_, ?_⟩
      · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (bitAtBody_nil mb) bitAtBody_wellScoped env)
        simpa [bitAtProg] using this
    · obtain ⟨tz, htz, hzr⟩ := isZeroProg_runs' mb []
      obtain ⟨mb', td, htd, hlen', hval, hd⟩ := decProg_runs' mb hz
      have hmb' : bitsVal mb' = m := by omega
      have hsy' : (encode ys).size ≤ sy := by
        simp only [encode_bitStr_cons, Data.size_cons] at hsy
        omega
      have hL' : mb'.length = L := hlen'.trans hL
      have hmbsize' : (encode mb').size ≤ 4 * L + 1 := by
        rw [← hL']; exact esize_bitStr_le mb'
      obtain ⟨t', ht', hrun⟩ := ih ys mb' hmb' hsy' hL' hmbsize'
      have hstep := Eval.append_of_wellScoped (bitAtBody_succ b ys mb mb' hz tz td hzr hd)
        bitAtBody_wellScoped env
      refine ⟨2 * (encode mb).size + tz + td + (encode ys).size + 14 + t' + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        have h2 : (ys.length + 1 + 1) * bitAtIter sy L =
            (ys.length + 1) * bitAtIter sy L + bitAtIter sy L := Nat.succ_mul _ _
        rw [hL] at htz htd
        omega
      · have := Eval.loop_step hstep hrun
        simpa [bitAtProg] using this
