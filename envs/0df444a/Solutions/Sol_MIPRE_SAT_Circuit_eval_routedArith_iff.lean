-- Prove2me | solution 1 for MIPRE.SAT.Circuit.eval_routedArith_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:34.044812+00:00
-- url     : https://prove2.me/submissions/4e1e7895-5dc8-4240-ac69-be7b0f315b6a

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (solution of MIPRE.SAT.Circuit.eval_routedArith_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Theorems.Thm_MIPRE_SAT_Circuit_eval_gateArith

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
variable [CharP F 2]
/-- In characteristic two, the factor is exactly the Boolean consistency indicator. -/
theorem eval_consistencyFactor (C : Circuit) (hC : C.WellFormed) (k : ℕ) (hk : k < C.size)
    (x w : ℕ → Bool) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      (C.consistencyFactor k) =
        if w k = (C.gates.getD k (.const false)).eval
          (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j)
        then 1 else 0 := by
  have href : ∀ u ∈ (C.gates.getD k (.const false)).refs, u < k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hC.refs_lt k hk
  rw [consistencyFactor, map_add, map_add, map_one, eval_X, eval_gateArith C k _ x w href]
  change 1 + ofBool (w k) + ofBool _ = _
  generalize (C.gates.getD k (.const false)).eval
    (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j) = b
  cases w k <;> cases b <;> simp [ofBool, CharTwo.add_self_eq_zero]
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
variable [CharP F 2]
theorem _root_.solution (C : Circuit) (hC : C.WellFormed) (x w : ℕ → Bool) :
    MvPolynomial.eval (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
      C.routedArith = 1 ↔ C.RoutedConsistent x w ∧ w (C.size - 1) = true := by
  rw [routedArith, map_mul, map_prod, eval_X]
  by_cases hc : C.RoutedConsistent x w
  · have hp : (∏ k ∈ range C.size, MvPolynomial.eval
        (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
        (C.consistencyFactor k)) = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      rw [eval_consistencyFactor C hC k (mem_range.mp hk) x w, if_pos (hc k (mem_range.mp hk))]
    rw [hp]
    simp only [one_mul, hc, true_and, Sum.elim_inr]
    cases w (C.size - 1) <;> simp [ofBool]
  · have hn : ∃ k, k < C.size ∧ w k ≠ (C.gates.getD k (.const false)).eval
        (fun i => Sum.elim x w (C.inputRef k i)) (List.ofFn fun j : Fin k => w j) := by
      simpa only [RoutedConsistent, not_forall, exists_prop] using hc
    obtain ⟨k, hk, he⟩ := hn
    have hp : (∏ k ∈ range C.size, MvPolynomial.eval
        (Sum.elim (fun i => (ofBool (x i) : F)) (fun j => ofBool (w j)))
        (C.consistencyFactor k)) = 0 := by
      apply Finset.prod_eq_zero (mem_range.mpr hk)
      rw [eval_consistencyFactor C hC k hk x w, if_neg he]
    simp [hp, hc]
end MIPRE.SAT.Circuit
