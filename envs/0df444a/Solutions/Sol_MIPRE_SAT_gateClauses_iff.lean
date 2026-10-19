-- Prove2me | solution 1 for MIPRE.SAT.gateClauses_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:51:34.223846+00:00
-- url     : https://prove2.me/submissions/c2bf4970-274c-48ce-951a-bc0b0dce5b4e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Tseitin.lean (solution of MIPRE.SAT.gateClauses_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
variable {V : Type*}
theorem _root_.solution (inp gv : ℕ → V) (y : V) (g : Gate) (w : V → Bool) (vals : List Bool)
    (hv : ∀ u ∈ g.refs, vals.getD u false = w (gv u)) :
    (∀ c ∈ gateClauses inp gv y g, c.eval w = true) ↔ w y = g.eval (fun i => w (inp i)) vals := by
  cases g with
  | input i =>
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval]
    cases w y <;> cases w (inp i) <;> simp
  | const b =>
    simp only [gateClauses, List.mem_singleton, forall_eq, Clause3.eval, cl, Lit.eval, Gate.eval]
    cases w y <;> cases b <;> simp
  | and u v =>
    have hu := hv u (by simp [Gate.refs])
    have hv' := hv v (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu, hv']
    cases w y <;> cases w (gv u) <;> cases w (gv v) <;> simp
  | or u v =>
    have hu := hv u (by simp [Gate.refs])
    have hv' := hv v (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu, hv']
    cases w y <;> cases w (gv u) <;> cases w (gv v) <;> simp
  | not u =>
    have hu := hv u (by simp [Gate.refs])
    simp only [gateClauses, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, Clause3.eval, cl, Lit.eval, Gate.eval, hu]
    cases w y <;> cases w (gv u) <;> simp
end MIPRE.SAT
