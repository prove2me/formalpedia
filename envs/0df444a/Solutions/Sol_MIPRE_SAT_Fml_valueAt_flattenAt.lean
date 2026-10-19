-- Prove2me | solution 1 for MIPRE.SAT.Fml.valueAt_flattenAt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:57.093957+00:00
-- url     : https://prove2.me/submissions/56769953-e6c4-41b7-b80e-d3ee798688cb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Formula.lean (solution of MIPRE.SAT.Fml.valueAt_flattenAt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_eq
import Theorems.Thm_MIPRE_SAT_Fml_size_pos

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
/-- The values of the earlier gates, as read by a gate. -/
theorem Circuit.getD_ofFn_valueAt (C : Circuit) (x : ℕ → Bool) (k u : ℕ) (hu : u < k) :
    (List.ofFn fun i : Fin k => C.valueAt x i).getD u false = C.valueAt x u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hu]
  rfl
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Fml
open Cost
theorem _root_.solution (n : ℕ) (x : ℕ → Bool) :
    ∀ (f : Fml) (pre post : List Gate),
      (Circuit.mk n (pre ++ f.flattenAt pre.length ++ post)).valueAt x (pre.length + f.size - 1) =
        f.eval x
  | inp i, pre, post => by
    simp only [flattenAt, size, Nat.add_sub_cancel]
    rw [Circuit.valueAt_eq]
    simp [List.getD_eq_getElem?_getD, eval, Gate.eval]
  | const b, pre, post => by
    simp only [flattenAt, size, Nat.add_sub_cancel]
    rw [Circuit.valueAt_eq]
    simp [List.getD_eq_getElem?_getD, eval, Gate.eval]
  | and f g, pre, post => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size - 1) = f.eval x := by
      have := solution n x f pre (g.flattenAt (pre.length + f.size) ++
        [Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hg : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size + g.size - 1) = g.eval x := by
      have := solution n x g (pre ++ f.flattenAt pre.length)
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.length_append, length_flattenAt, List.append_assoc] at this
      exact this
    have hlist : pre ++ (and f g).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
          ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + g.size + 1) - 1 = pre.length + f.size + g.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))[
          pre.length + f.size + g.size]? =
        some (Gate.and (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size + g.size - pre.length - (f.flattenAt pre.length).length -
          (g.flattenAt (pre.length + f.size)).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Circuit.getD_ofFn_valueAt _ _ _ _ (by omega),
      hf, hg]
  | or f g, pre, post => by
    have hfp := f.size_pos
    have hgp := g.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size - 1) = f.eval x := by
      have := solution n x f pre (g.flattenAt (pre.length + f.size) ++
        [Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hg : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))).valueAt x
          (pre.length + f.size + g.size - 1) = g.eval x := by
      have := solution n x g (pre ++ f.flattenAt pre.length)
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post)
      simp only [List.length_append, length_flattenAt, List.append_assoc] at this
      exact this
    have hlist : pre ++ (or f g).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
          ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + g.size + 1) - 1 = pre.length + f.size + g.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ (g.flattenAt (pre.length + f.size) ++
        ([Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)] ++ post))))[
          pre.length + f.size + g.size]? =
        some (Gate.or (pre.length + f.size - 1) (pre.length + f.size + g.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size + g.size - pre.length - (f.flattenAt pre.length).length -
          (g.flattenAt (pre.length + f.size)).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), Circuit.getD_ofFn_valueAt _ _ _ _ (by omega),
      hf, hg]
  | not f, pre, post => by
    have hfp := f.size_pos
    have hf : (Circuit.mk n (pre ++ (f.flattenAt pre.length ++
        ([Gate.not (pre.length + f.size - 1)] ++ post)))).valueAt x (pre.length + f.size - 1) =
          f.eval x := by
      have := solution n x f pre ([Gate.not (pre.length + f.size - 1)] ++ post)
      simp only [List.append_assoc] at this
      exact this
    have hlist : pre ++ (not f).flattenAt pre.length ++ post =
        pre ++ (f.flattenAt pre.length ++ ([Gate.not (pre.length + f.size - 1)] ++ post)) := by
      simp [flattenAt]
    rw [hlist]
    rw [Circuit.valueAt_eq]
    simp only [size, List.getD_eq_getElem?_getD]
    have hk : pre.length + (f.size + 1) - 1 = pre.length + f.size := by omega
    rw [hk]
    have hget : (pre ++ (f.flattenAt pre.length ++ ([Gate.not (pre.length + f.size - 1)] ++ post)))[
          pre.length + f.size]? = some (Gate.not (pre.length + f.size - 1)) := by
      rw [List.getElem?_append_right (by (try simp only [length_flattenAt]); omega),
        List.getElem?_append_right (by (try simp only [length_flattenAt]); omega)]
      have h0 : pre.length + f.size - pre.length - (f.flattenAt pre.length).length = 0 := by
        simp only [length_flattenAt]; omega
      rw [h0]; rfl
    rw [hget]
    simp only [Option.getD_some, Gate.eval, eval]
    rw [Circuit.getD_ofFn_valueAt _ _ _ _ (by omega), hf]
end MIPRE.SAT.Fml
