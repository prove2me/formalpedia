-- Prove2me | solution 1 for MIPRE.Cost.whileProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:50.58807+00:00
-- url     : https://prove2.me/submissions/377b1ba8-e239-40f1-aa02-c0c22efdffac

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/While.lean (solution of MIPRE.Cost.whileProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_While

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
open PolyTimeFun
theorem _root_.solution (f : PolyTimeFun Data (Bool × Data)) (N : ℕ) (s : ℕ → Data) (r : Data)
    (hcont : ∀ i < N, f (s i) = (true, s (i + 1))) (hstop : f (s N) = (false, r)) :
    ∃ t ≤ ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s i).size + 1),
      (whileProg f).Runs (s 0) r t := by
  induction N generalizing s with
  | zero =>
    obtain ⟨t, ht, hr⟩ := f.computes (s 0)
    rw [hstop] at hr
    refine ⟨t + 1, by simpa using ht, ?_⟩
    exact Eval.loop_stop (b := f.code) (env := [s 0]) (r := r) hr
  | succ N ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := f.computes (s 0)
    rw [hcont 0 (by omega)] at h₀
    obtain ⟨t, ht, hrun⟩ := ih (fun i => s (i + 1)) (fun i hi => hcont (i + 1) (by omega)) hstop
    refine ⟨t₀ + t + 1, ?_, Eval.loop_step (x := .nil) (y := .nil) h₀ hrun⟩
    rw [Finset.sum_range_succ']
    simp only [esize_data] at ht₀
    have : ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s (i + 1)).size + 1) ≥ t := ht
    omega
end MIPRE.Cost
