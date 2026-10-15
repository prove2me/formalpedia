-- Prove2me | solution 1 for MIPRE.Cost.Machine.clockRun_of_not
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:59:58.073697+00:00
-- url     : https://prove2.me/submissions/e3781a3b-fe31-4a16-9ebb-bd164875efcd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.clockRun_of_not);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Theorems.Thm_MIPRE_Cost_Machine_eval_of_steps

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Machine
theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem costSum_le_of_le (c : Cfg) {m n : ℕ} (h : m ≤ n) : costSum c m ≤ costSum c n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [costSum_add]; omega
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c : Prog) (v : Data) (k Θ : ℕ)
    (hno : ¬ ∃ r t, t ≤ k ∧ c.Runs v r t) :
    ∀ b n, costSum ⟨.ev c, [v], []⟩ n ≤ k → clockRun ⟨.ev c, [v], []⟩ k Θ b n = .nil := by
  have hnf : ∀ n, costSum ⟨.ev c, [v], []⟩ n ≤ k → ¬ IsFinal (step^[n] ⟨.ev c, [v], []⟩) := by
    rintro n hn ⟨r, e, hr⟩
    obtain ⟨r', t', M, e', N', hM, hev, hs⟩ := eval_of_steps n c [v] [] r e hr
    refine hno ⟨r', t', ?_, hev⟩
    have := costSum_le_of_le ⟨.ev c, [v], []⟩ (show M ≤ n by omega)
    rw [hs.2] at this
    omega
  intro b
  induction b with
  | zero => intro n hn; simp only [clockRun, if_neg (hnf n hn)]
  | succ b ih =>
    intro n hn
    simp only [clockRun, if_neg (hnf n hn)]
    split_ifs with h
    · exact ih (n + 1) h.1
    · rfl
