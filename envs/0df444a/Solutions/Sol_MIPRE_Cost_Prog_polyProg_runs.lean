-- Prove2me | solution 1 for MIPRE.Cost.Prog.polyProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:37.715297+00:00
-- url     : https://prove2.me/submissions/2b04617f-bcbe-4542-be1a-19d3edfc7f79

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (solution of MIPRE.Cost.Prog.polyProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Theorems.Thm_MIPRE_Cost_Prog_mulLoop_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
theorem mulProg_wellScoped : mulProg.WellScoped 1 := by
  simp [mulProg, WellScoped, mulBody, addProg, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
/-- `mulProg` multiplies unary numerals. -/
theorem mulProg_runs (a b : ℕ) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
        2 * b + 10,
      mulProg.Runs (Data.cons (ofNat a) (ofNat b)) (ofNat (a * b)) t := by
  obtain ⟨t, ht, hrun⟩ := mulLoop_runs a b 0 [ofNat b, Data.cons (ofNat a) (ofNat b)] (a * b)
    (by omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
    (i := 1) (v := ofNat b) (by simp)) (Eval.nil [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
  have hrun' : Eval (Data.cons (ofNat b) Data.nil :: [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
      (.loop mulBody) (ofNat (a * b)) t := by simpa [ofNat] using hrun
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat a) (b := ofNat b) (by simp)
    (Eval.let_ hpre hrun')⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem _root_.solution (cs : List ℕ) :
    ∃ Q : Polynomial ℕ, ∀ (m : ℕ) (env : Env),
      ∃ t ≤ Q.eval m, Eval (ofNat m :: env) (polyProg cs) (ofNat (polyEval cs m)) t := by
  induction cs with
  | nil => exact ⟨C 1, fun m env => ⟨1, by simp, Eval.nil _⟩⟩
  | cons c cs ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q + (Q + 1) * ((X + 1) * (4 * X + 2 * X * Q + 15) + 4 * X + 4 * X * Q + 2 * Q + 41) +
      (C c + 1) * (4 * C c + 2 * X * Q + 15) + 4 * X * Q + 4 * X + 4 * Q + C (4 * c) + 40,
      fun m env => ?_⟩
    obtain ⟨t₁, ht₁, h₁⟩ := hQ m env
    set p := polyEval cs m with hp
    have hpQ : p ≤ Q.eval m := by
      have := h₁.size_le
      simp only [Data.size_ofNat] at this
      omega
    obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs m p
    obtain ⟨t₃, ht₃, h₃⟩ := addProg_runs c (m * p) [ofNat (m * p), ofNat p, ofNat m]
    -- the pair `(m, p)` and the product
    have hpair : Eval [ofNat p, ofNat m] (.cons (.var 1) (.var 0)) (Data.cons (ofNat m) (ofNat p))
        ((ofNat m).size + 1 + ((ofNat p).size + 1) + 1) :=
      Eval.cons (Eval.var_of_get (i := 1) (v := ofNat m) (by simp))
        (Eval.var_of_get (i := 0) (v := ofNat p) (by simp))
    have hmul := Eval.let_ hpair (Eval.append_of_wellScoped h₂ mulProg_wellScoped [ofNat p, ofNat m])
    -- the pair `(c, m p)` and the sum
    have hpair' : Eval [ofNat (m * p), ofNat p, ofNat m] (.cons (.const (ofNat c)) (.var 0))
        (Data.cons (ofNat c) (ofNat (m * p))) ((ofNat c).size + ((ofNat (m * p)).size + 1) + 1) :=
      Eval.cons (Eval.const _ _) (Eval.var_of_get (i := 0) (v := ofNat (m * p)) (by simp))
    have hadd := Eval.let_ hpair' h₃
    have hbody : Eval [ofNat p, ofNat m] (.let_ (.let_ (.cons (.var 1) (.var 0)) mulProg)
        (.let_ (.cons (.const (ofNat c)) (.var 0)) addProg)) (ofNat (c + m * p)) _ :=
      Eval.let_ hmul hadd
    have hbody' := Eval.append_of_wellScoped hbody
      (by simp [WellScoped, mulProg, mulBody, addProg, lenBody]) env
    refine ⟨_, ?_, Eval.let_ h₁ (by simpa [polyEval, hp] using hbody')⟩
    simp only [eval_add, eval_mul, eval_X, eval_C, eval_one, eval_ofNat]
    have hprod : m * p ≤ m * Q.eval m := Nat.mul_le_mul_left _ hpQ
    have hmulle : (p + 1) * ((m + 1) * (4 * m + 2 * (m * p) + 15) + 4 * m + 4 * (m * p) + 2 * p + 41) ≤
        (Q.eval m + 1) * ((m + 1) * (4 * m + 2 * (m * Q.eval m) + 15) + 4 * m + 4 * (m * Q.eval m) +
          2 * Q.eval m + 41) :=
      Nat.mul_le_mul (by omega) (by nlinarith)
    have haddle : (c + 1) * (4 * c + 2 * (m * p) + 15) ≤ (c + 1) * (4 * c + 2 * (m * Q.eval m) + 15) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [Data.size_ofNat] at *
    nlinarith
end MIPRE.Cost.Prog
