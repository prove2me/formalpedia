-- Prove2me | solution 1 for MIPRE.Cost.Prog.normBinProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:19:02.370644+00:00
-- url     : https://prove2.me/submissions/5c149a48-fe99-4f7c-8930-a93043bd96ff

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (solution of MIPRE.Cost.Prog.normBinProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Theorems.Thm_MIPRE_Cost_Data_canonWalk_eq_isCanonBin
import Theorems.Thm_MIPRE_Cost_Prog_canonLoop_runs

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (d : Data) :
    ∃ t ≤ (d.spine + 2) * (d.size + 25) + 3 * d.size + 10,
      normBinProg.Runs d (normBin d) t := by
  obtain ⟨t, ht, hrun⟩ := canonLoop_runs d true [d] (d.size + 3) le_rfl
  have hpre := Eval.cons (Eval.var_of_get (env := [d]) (i := 0) (v := d) (by simp))
    (Eval.cons (Eval.nil [d]) (Eval.nil [d]))
  have hloop := Eval.let_ hpre hrun
  rw [canonWalk_eq_isCanonBin] at hloop
  have hmul : (d.spine + 1) * (d.size + 3 + 21) ≤ (d.spine + 2) * (d.size + 25) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold normBin
  rcases hc : isCanonBin d
  · rw [hc] at hloop
    have hget : Env.get [encode false, d] 0 = Data.nil := by simp [encode_bool, ofBool]
    refine ⟨_, ?_, Eval.let_ hloop (Eval.elim_nil (i := 0) hget (Eval.nil _))⟩
    omega
  · rw [hc] at hloop
    have hget : Env.get [encode true, d] 0 = Data.cons Data.nil Data.nil := by
      simp [encode_bool, ofBool]
    refine ⟨_, ?_, Eval.let_ hloop (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) hget
      (Eval.var_of_get (env := [Data.nil, Data.nil, encode true, d]) (i := 3) (v := d) (by simp)))⟩
    omega
end MIPRE.Cost.Prog
