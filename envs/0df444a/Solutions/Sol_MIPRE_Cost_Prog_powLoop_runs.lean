-- Prove2me | solution 1 for MIPRE.Cost.Prog.powLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:33:57.814251+00:00
-- url     : https://prove2.me/submissions/25c06500-f490-49cf-a96b-c8906f71b311

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Prims.lean (solution of MIPRE.Cost.Prog.powLoop_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Theorems.Thm_MIPRE_Cost_Prog_powBody_step

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem powBody_wellScoped : powBody.WellScoped 1 := by
  simp [powBody, WellScoped, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem powBody_stop (bl bn acc : List Data) :
    ∃ t ≤ (Data.list acc).size + 8,
      Eval [powState 0 bl bn acc] powBody (.cons .nil (.list acc)) t := by
  have run : Eval [powState 0 bl bn acc] powBody (.cons .nil (.list acc)) _ :=
    Eval.elim_cons (env := [powState 0 bl bn acc]) (i := 0) (n := .nil)
      (a := ofNat 0) (b := .cons (.list bl) (.cons (.list bn) (.list acc))) (by simp [powState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (Eval.elim_cons (i := 1) (n := .nil) (a := .list bl) (b := .cons (.list bn) (.list acc))
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := .list bn) (b := .list acc) (by simp)
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := .list acc) (by simp))))))
  exact ⟨_, by omega, run⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
/-- The size of a list of `m` copies of `nil` in front of `acc`. -/
theorem size_list_replicate_nil_append (m : ℕ) (acc : List Data) :
    (Data.list (List.replicate m .nil ++ acc)).size = 2 * m + (Data.list acc).size := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.cons_append, Data.size_list_cons, ih]; simp; omega
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (e : ℕ) (bl bn acc : List Data) (env : Env) :
    ∃ t ≤ powCost e (bl.length + bn.length)
        ((Data.list bl).size + (Data.list bn).size + (Data.list acc).size),
      Eval (powState e bl bn acc :: env) (.loop powBody)
        (.list (List.replicate (e * (bl.length + bn.length)) .nil ++ acc)) t := by
  induction e generalizing acc with
  | zero =>
    obtain ⟨t, ht, h⟩ := powBody_stop bl bn acc
    refine ⟨t + 1, ?_, ?_⟩
    · unfold powCost
      nlinarith [Nat.zero_le ((bl.length + bn.length) * (Data.list acc).size),
        Nat.zero_le ((bl.length + bn.length) * ((Data.list bl).size + (Data.list bn).size))]
    · simpa using Eval.loop_stop (Eval.append_of_wellScoped h powBody_wellScoped env)
  | succ e ih =>
    obtain ⟨t₁, ht₁, h₁⟩ := powBody_step e bl bn acc
    obtain ⟨t₂, ht₂, h₂⟩ := ih (List.replicate (bl.length + bn.length) .nil ++ acc)
    have hres : List.replicate (e * (bl.length + bn.length)) .nil ++
        (List.replicate (bl.length + bn.length) .nil ++ acc) =
        List.replicate ((e + 1) * (bl.length + bn.length)) .nil ++ acc := by
      rw [← List.append_assoc, ← List.replicate_add]; congr 2; ring
    rw [hres] at h₂
    refine ⟨t₁ + t₂ + 1, ?_,
      Eval.loop_step (Eval.append_of_wellScoped h₁ powBody_wellScoped env) h₂⟩
    rw [size_list_replicate_nil_append] at ht₂
    set L := bl.length + bn.length with hL
    set sz := (Data.list bl).size + (Data.list bn).size + (Data.list acc).size with hsz
    set D : ℕ := 8 * (L + 1) * (sz + 2 * (e + 1) * L + (e + 1) + 14) with hD
    have hbl : bl.length ≤ L := by omega
    have hbn : bn.length ≤ L := by omega
    -- the step is below one round's budget
    have hstep : t₁ + 1 ≤ D := by
      rw [hD]
      have h1 : (bn.length + 1) * (sz + 2 * bn.length + 13) ≤ (L + 1) * (sz + 2 * L + 13) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (bl.length + 1) * (sz + 2 * bn.length + 2 * bl.length + 13) ≤
          (L + 1) * (sz + 2 * L + 13) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : 4 * (sz + 2 * e + 2 * bn.length + 2 * bl.length) ≤ 4 * (sz + 2 * e + 2 * L) := by
        omega
      have h4 : (L + 1) * (sz + 2 * L + 13) + (L + 1) * (sz + 2 * L + 13) + 4 * (sz + 2 * e + 2 * L) +
          40 < 8 * (L + 1) * (sz + 2 * (e + 1) * L + (e + 1) + 14) := by
        nlinarith [Nat.zero_le (L * sz), Nat.zero_le (L * L), Nat.zero_le (L * e), Nat.zero_le (e * L * L)]
      omega
    -- the remaining rounds are below their budgets
    have hrest : t₂ ≤ (e + 1) * D := by
      refine ht₂.trans ?_
      unfold powCost
      rw [hD]
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
      rw [hsz]
      nlinarith
    unfold powCost
    rw [← hD, Nat.succ_mul]
    omega
end MIPRE.Cost.Prog
