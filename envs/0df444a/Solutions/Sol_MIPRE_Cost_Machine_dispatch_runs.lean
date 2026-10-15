-- Prove2me | solution 1 for MIPRE.Cost.Machine.dispatch_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:41:15.062842+00:00
-- url     : https://prove2.me/submissions/80d51634-1571-4625-ac64-2feb3c6b528e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Interpreter.lean (solution of MIPRE.Cost.Machine.dispatch_runs);
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open MIPRE.Cost.Prog
theorem solution : ∀ (cs : List Prog) (k i idx : ℕ) (E : Env) (pk r : Data) (t : ℕ),
    k < cs.length → (∀ c ∈ cs, c.WellScoped 1) → E.get i = Data.ofNat k → E.get idx = pk →
    Eval [pk] (cs.getD k .nil) r t →
    ∃ s ≤ t + pk.size + k + 3, Eval E (dispatch cs i idx) r s
  | [], k, _, _, _, _, _, _, hk, _, _, _, _ => by simp at hk
  | [c], k, i, idx, E, pk, r, t, hk, hcs, hi, hidx, h => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨_, by omega, callVar_eval (i := idx) (hcs c (by simp)) hidx h⟩
  | c :: c' :: cs, k, i, idx, E, pk, r, t, hk, hcs, hi, hidx, h => by
    cases k with
    | zero =>
      exact ⟨_, by omega, Eval.elim_nil (i := i) hi (callVar_eval (i := idx) (hcs c (by simp)) hidx h)⟩
    | succ k' =>
      obtain ⟨s, hs, hd⟩ := solution (c' :: cs) k' 1 (idx + 2) (Data.nil :: Data.ofNat k' :: E)
        pk r t (by simp at hk ⊢; omega) (fun d hd => hcs d (List.mem_cons_of_mem c hd))
        (by simp) (by simpa using hidx) (by simpa using h)
      exact ⟨_, by omega, Eval.elim_cons (i := i) (a := .nil) (b := .ofNat k')
        (by rw [hi]; rfl) hd⟩
