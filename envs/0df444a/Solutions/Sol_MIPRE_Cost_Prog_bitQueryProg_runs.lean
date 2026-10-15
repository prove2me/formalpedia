-- Prove2me | solution 1 for MIPRE.Cost.Prog.bitQueryProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:51:49.112112+00:00
-- url     : https://prove2.me/submissions/27e59938-52e2-4282-81aa-0a01e78003e3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Succinct.lean (solution of MIPRE.Cost.Prog.bitQueryProg_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Theorems.Thm_MIPRE_Cost_Prog_bitAtLoop_runs

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

namespace MIPRE.Cost
theorem esize_nat_le (n : ℕ) : esize n ≤ 4 * Nat.size n + 1 := by
  have := esize_bitStr_le n.bits
  rw [Nat.size_eq_bits_len] at this
  exact this
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
theorem bitsVal_bits (n : ℕ) : bitsVal n.bits = n := Nat.foldr_bit_bits n
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
theorem bitAtBody_wellScoped : bitAtBody.WellScoped 1 := by
  refine ⟨by decide, trivial, by decide, ⟨trivial, trivial⟩, ?_⟩
  refine ⟨callVar_wellScoped (by decide) isZeroProg_wellScoped, ?_⟩
  refine ⟨by decide, ⟨trivial, by simp [WellScoped]⟩, ⟨trivial, trivial⟩,
    ⟨by simp [WellScoped], ?_⟩⟩
  exact callVar_wellScoped (by decide) decProg_wellScoped
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem bitAtProg_wellScoped : bitAtProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitAtBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- `bitAtProg` answers bit queries: on `(encode y, encode m)` it computes
`bitQueryAnswer y m`, in time `(|y| + 1) · bitAtIter (size y) (Nat.size m)`. -/
theorem bitAtProg_runs (y : BitStr) (m : ℕ) :
    ∃ t ≤ (y.length + 1) * bitAtIter (encode y).size (Nat.size m),
      bitAtProg.Runs (.cons (encode y) (encode m)) (bitQueryAnswer y m) t :=
  bitAtLoop_runs m y m.bits (bitsVal_bits m) [] (encode y).size (Nat.size m) le_rfl
    (Nat.size_eq_bits_len m)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
/-- `bitAtIter` is quadratic in the length of the index. -/
theorem bitAtIter_le (sy L : ℕ) : bitAtIter sy L ≤ (sy + 534) * (L + 1) ^ 2 := by
  unfold bitAtIter zeroBound decBound
  nlinarith [Nat.zero_le sy, Nat.zero_le L, Nat.zero_le (sy * L), Nat.zero_le (sy * (L * L)),
    Nat.zero_le (L * L)]
end MIPRE.Cost.Prog

namespace MIPRE.Cost
open Polynomial
theorem bitQueryBound_eval (U : UniversalMachine) (s : ℕ) :
    (bitQueryBound U).eval s = U.bound.eval (s + 1) + (s + 1) * (s + 534) + 2 * s + 29 := by
  simp [bitQueryBound, Polynomial.eval_comp]
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
theorem solution (U : UniversalMachine) {α : Type*} [SizedEncoding α]
    (c' e : Prog) (n : α) (y : BitStr) (m : ℕ) {t : ℕ}
    (hrun : c'.Runs (encode (e, n)) (encode y) t) :
    ∃ T ≤ (bitQueryBound U).eval (esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2,
      (bitQueryProg U.univ).Runs (encode (((c', e), n), m)) (bitQueryAnswer y m) T := by
  obtain ⟨t', ht', h'⟩ := U.time_le c' (encode (e, n)) (encode y) t hrun
  obtain ⟨tb, htb, hb⟩ := bitAtProg_runs y m
  -- the run
  have s1 : Eval [encode c', encode e, Data.cons (encode c') (encode e), encode n,
      Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
      Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)]
      (.cons (.var 0) (.cons (.var 1) (.var 3)))
      (.cons (encode c') (.cons (encode e) (encode n))) _ :=
    Eval.cons (Eval.var_of_get (i := 0) (v := encode c') (by simp))
      (Eval.cons (Eval.var_of_get (i := 1) (v := encode e) (by simp))
        (Eval.var_of_get (i := 3) (v := encode n) (by simp)))
  have s2 := callVar_eval
    (env := Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) U.closed (v := .cons (encode c') (.cons (encode e) (encode n))) (by simp) h'
  have s3 : Eval (encode y :: Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
      (.cons (.var 0) (.var 7)) (.cons (encode y) (encode m)) _ :=
    Eval.cons (Eval.var_of_get (i := 0) (v := encode y) (by simp))
      (Eval.var_of_get (i := 7) (v := encode m) (by simp))
  have s4 := callVar_eval
    (env := Data.cons (encode y) (encode m) :: encode y ::
      Data.cons (encode c') (.cons (encode e) (encode n)) ::
      [encode c', encode e, Data.cons (encode c') (encode e), encode n,
        Data.cons (Data.cons (encode c') (encode e)) (encode n), encode m,
        Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) bitAtProg_wellScoped (v := .cons (encode y) (encode m)) (by simp) hb
  have run := Eval.elim_cons
    (env := [Data.cons (Data.cons (Data.cons (encode c') (encode e)) (encode n)) (encode m)])
    (i := 0) (n := .nil) (a := .cons (.cons (encode c') (encode e)) (encode n)) (b := encode m)
    (by simp)
    (Eval.elim_cons (i := 0) (n := .nil) (a := .cons (encode c') (encode e)) (b := encode n)
      (by simp)
      (Eval.elim_cons (i := 0) (n := .nil) (a := encode c') (b := encode e) (by simp)
        (Eval.let_ s1 (Eval.let_ s2 (Eval.let_ s3 s4)))))
  refine ⟨_, ?_, run⟩
  -- the bound
  rw [bitQueryBound_eval]
  have e1 : (encode (e, n)).size = esize e + esize n + 1 := rfl
  have e2 : (encode c').size = esize c' := rfl
  have e3 : (encode e).size = esize e := rfl
  have e4 : (encode n).size = esize n := rfl
  have hsy : (encode y).size ≤ t := hrun.size_le
  have hly : y.length ≤ (encode y).size := length_le_esize_bitStr y
  have hsm : (encode m).size ≤ 4 * Nat.size m + 1 := esize_nat_le m
  have hP1 : Nat.size m + 1 ≤ (Nat.size m + 1) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_self _
  have hB : t' ≤ U.bound.eval (esize c' + esize e + esize n + t + 1) :=
    ht'.trans (polynomial_eval_mono U.bound (by omega))
  have hb' : tb ≤ (esize c' + esize e + esize n + t + 1) *
      (esize c' + esize e + esize n + t + 534) * (Nat.size m + 1) ^ 2 := by
    calc tb ≤ (y.length + 1) * bitAtIter (encode y).size (Nat.size m) := htb
      _ ≤ (esize c' + esize e + esize n + t + 1) *
          ((esize c' + esize e + esize n + t + 534) * (Nat.size m + 1) ^ 2) :=
        Nat.mul_le_mul (by omega)
          ((bitAtIter_le _ _).trans (Nat.mul_le_mul_right _ (by omega)))
      _ = _ := by ring
  have hexp : (U.bound.eval (esize c' + esize e + esize n + t + 1) +
      (esize c' + esize e + esize n + t + 1) * (esize c' + esize e + esize n + t + 534) +
      2 * (esize c' + esize e + esize n + t) + 29) * (Nat.size m + 1) ^ 2 =
      U.bound.eval (esize c' + esize e + esize n + t + 1) * (Nat.size m + 1) ^ 2 +
      (esize c' + esize e + esize n + t + 1) * (esize c' + esize e + esize n + t + 534) *
        (Nat.size m + 1) ^ 2 +
      2 * ((esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2) +
      29 * (Nat.size m + 1) ^ 2 := by ring
  have hBP : U.bound.eval (esize c' + esize e + esize n + t + 1) ≤
      U.bound.eval (esize c' + esize e + esize n + t + 1) * (Nat.size m + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
  have hsP : esize c' + esize e + esize n + t ≤
      (esize c' + esize e + esize n + t) * (Nat.size m + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) 2)
  simp only [Data.size_cons]
  omega
