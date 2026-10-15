-- Prove2me | solution 1 for MIPRE.Cost.Machine.clockRun_of_final
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:59:25.510988+00:00
-- url     : https://prove2.me/submissions/ee56f5ff-99ab-4265-b83b-2ef6f314e2ee

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.clockRun_of_final);
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
theorem step_final (r : Data) (e : Env) (n : ℕ) :
    step^[n] (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n
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
theorem solution (c₀ : Cfg) (k Θ : ℕ) (N : ℕ) (r : Data) (e : Env)
    (hN : step^[N] c₀ = ⟨.ret r, e, []⟩) (hcost : costSum c₀ N ≤ k)
    (hΘ : ∀ n, (step^[n] c₀).toData.size ≤ Θ) :
    ∀ b n, n ≤ N → N ≤ n + b → clockRun c₀ k Θ b n = .cons (.cons .nil .nil) r := by
  intro b
  induction b with
  | zero =>
    intro n h1 h2
    have hn : n = N := by omega
    subst hn
    simp only [clockRun, if_pos (show IsFinal (step^[n] c₀) from ⟨r, e, hN⟩), hN, Cfg.val]
  | succ b ih =>
    intro n h1 h2
    by_cases hf : IsFinal (step^[n] c₀)
    · obtain ⟨r', e', hr'⟩ := id hf
      have hN' : (⟨.ret r, e, []⟩ : Cfg) = ⟨.ret r', e', []⟩ := by
        rw [← hN, show N = (N - n) + n by omega, Function.iterate_add_apply, hr', step_final]
      obtain ⟨rfl, rfl⟩ : r = r' ∧ e = e' := by simpa using hN'
      simp only [clockRun, if_pos hf, hr', Cfg.val]
    · have hlt : n < N := by
        rcases Nat.lt_or_ge n N with h | h
        · exact h
        · exact absurd ⟨r, e, by
            rw [show n = (n - N) + N by omega, Function.iterate_add_apply, hN, step_final]⟩ hf
      have hc : costSum c₀ (n + 1) ≤ k :=
        (costSum_le_of_le c₀ (show n + 1 ≤ N by omega)).trans hcost
      simp only [clockRun, if_neg hf, if_pos (And.intro hc (hΘ (n + 1)))]
      exact ih (n + 1) (by omega) (by omega)
