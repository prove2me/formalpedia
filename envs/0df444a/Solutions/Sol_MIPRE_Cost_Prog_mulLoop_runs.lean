-- Prove2me | solution 1 for MIPRE.Cost.Prog.mulLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:51.800374+00:00
-- url     : https://prove2.me/submissions/0984fd81-703d-41de-bc14-63e986400f7d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (solution of MIPRE.Cost.Prog.mulLoop_runs);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
theorem mulBody_nil (a acc : ℕ) (rest : Env) :
    ∃ t ≤ 2 * acc + 20,
      Eval (Data.cons (ofNat 0) (ofNat acc) :: ofNat a :: rest) mulBody
        (Data.cons Data.nil (ofNat acc)) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat 0) (b := ofNat acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp [ofNat])
      (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := ofNat acc) (by simp))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
theorem mulBody_step (a b' acc : ℕ) (rest : Env) :
    ∃ t ≤ (a + 1) * (4 * a + 2 * acc + 15) + 4 * a + 4 * acc + 2 * b' + 40,
      Eval (Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) mulBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (ofNat b') (ofNat (a + acc)))) t := by
  obtain ⟨t₀, ht₀, hadd⟩ := addProg_runs a acc
    (Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest)
  have hpair := Eval.cons
    (Eval.var_of_get (env := Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) (i := 5) (v := ofNat a) (by simp))
    (Eval.var_of_get (env := Data.nil :: ofNat b' :: ofNat (b' + 1) :: ofNat acc ::
      Data.cons (ofNat (b' + 1)) (ofNat acc) :: ofNat a :: rest) (i := 3) (v := ofNat acc) (by simp))
  have hsum := Eval.let_ hpair hadd
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat (b' + 1)) (b := ofNat acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := ofNat b') (by simp [ofNat])
      (Eval.let_ (by simpa using hsum)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 2) (v := ofNat b') (by simp))
            (Eval.var_of_get (i := 0) (v := ofNat (a + acc)) (by simp))))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem _root_.solution (a b acc : ℕ) (rest : Env) (P : ℕ) (hP : acc + a * b ≤ P) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41),
      Eval (Data.cons (ofNat b) (ofNat acc) :: ofNat a :: rest) (.loop mulBody)
        (ofNat (acc + a * b)) t := by
  induction b generalizing acc with
  | zero =>
    obtain ⟨t, ht, hrun⟩ := mulBody_nil a acc rest
    refine ⟨t + 1, ?_, by simpa using Eval.loop_stop hrun⟩
    simp only [Nat.mul_zero, Nat.add_zero] at hP
    nlinarith
  | succ b ih =>
    obtain ⟨t, ht, hrun⟩ := mulBody_step a b acc rest
    have hP' : a + acc + a * b ≤ P := by rw [Nat.mul_succ] at hP; omega
    obtain ⟨t', ht', hrun'⟩ := ih (a + acc) hP'
    refine ⟨t + t' + 1, ?_, ?_⟩
    · have hacc : acc ≤ P := by nlinarith
      have h2 : (b + 1 + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) =
          (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) +
            ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) := Nat.succ_mul _ _
      have h3 : (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41) ≤
          (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * (b + 1) + 41) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : (a + 1) * (4 * a + 2 * acc + 15) ≤ (a + 1) * (4 * a + 2 * P + 15) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    · have := Eval.loop_step hrun hrun'
      rw [Nat.mul_succ]
      rw [show acc + (a * b + a) = a + acc + a * b by ring]
      exact this
end MIPRE.Cost.Prog
