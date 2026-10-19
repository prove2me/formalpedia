-- Prove2me | solution 1 for MIPRE.SAT.Circuit.degreeOf_routedArith_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:33.422031+00:00
-- url     : https://prove2.me/submissions/64441ce3-3f36-4819-a8cd-59ece35659de

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (solution of MIPRE.SAT.Circuit.degreeOf_routedArith_le);
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
import Theorems.Thm_MIPRE_SAT_Circuit_sum_inputWeight_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem degreeOf_gateArith (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) :
    (C.gateArith (F := F) k (C.gates.getD k (.const false))).degreeOf v ≤
      C.inputWeight k v + refWeight (C.gates.getD k (.const false)) v := by
  unfold inputWeight
  generalize C.gates.getD k (.const false) = g
  cases g with
  | input i => cases v <;> simp [gateArith, refWeight, Gate.refs, degreeOf_X]
  | const b => cases v <;> simp [gateArith, refWeight, Gate.refs]
  | and u w =>
    have h := degreeOf_mul_le v (X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) (X (.inr w))
    cases v <;> simpa [gateArith, refWeight, Gate.refs, count_pair, degreeOf_X] using h
  | or u w =>
    have ha := degree_one_sub (F := F) ((1 - X (.inr u)) * (1 - X (.inr w))) v
    have hb := degreeOf_mul_le v (1 - X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) (1 - X (.inr w))
    have hc := Nat.add_le_add (degree_one_sub (F := F) (X (.inr u)) v)
      (degree_one_sub (F := F) (X (.inr w)) v)
    have h := ha.trans (hb.trans hc)
    cases v <;> simpa [gateArith, refWeight, Gate.refs, count_pair, degreeOf_X] using h
  | not u =>
    have h := degree_one_sub (X (.inr u) : MvPolynomial (ℕ ⊕ ℕ) F) v
    cases v with
    | inl i => simpa [gateArith, refWeight, Gate.refs, degreeOf_X] using h
    | inr j =>
      by_cases hu : u = j <;> simpa [gateArith, refWeight, Gate.refs, degreeOf_X, hu, eq_comm] using h
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem degreeOf_consistencyFactor (C : Circuit) (k : ℕ) (v : ℕ ⊕ ℕ) :
    (C.consistencyFactor (F := F) k).degreeOf v ≤
      (if v = .inr k then 1 else 0) + C.inputWeight k v +
        refWeight (C.gates.getD k (.const false)) v := by
  have h := degreeOf_gateArith (F := F) C k v
  have h' := degreeOf_add_le v (1 + X (.inr k))
    (C.gateArith (F := F) k (C.gates.getD k (.const false)))
  have h₀ := degreeOf_add_le v (1 : MvPolynomial (ℕ ⊕ ℕ) F) (X (.inr k))
  simp only [degreeOf_one, degreeOf_X, zero_le, max_eq_right] at h₀
  change _ ≤ _ at h'
  unfold consistencyFactor
  exact h'.trans (max_le (by omega) (by omega))
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem sum_refWeight (C : Circuit) (v : ℕ ⊕ ℕ) :
    ∑ k ∈ range C.size, refWeight (C.gates.getD k (.const false)) v =
      match v with | .inl _ => 0 | .inr j => C.fanout j := by
  rw [show C.size = C.gates.length from rfl, sum_getD C.gates (fun g => refWeight g v)]
  cases v with
  | inl i => simp [refWeight]
  | inr j => rfl
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem _root_.solution (C : Circuit) (hC : C.WellFormed) (v : ℕ ⊕ ℕ) :
    (C.routedArith (F := F)).degreeOf v ≤ 5 := by
  have hf := degreeOf_mul_le v
    (∏ k ∈ range C.size, C.consistencyFactor (F := F) k) (X (.inr (C.size - 1)))
  have hp := (degreeOf_prod_le v (range C.size) (fun k => C.consistencyFactor (F := F) k)).trans
    (Finset.sum_le_sum (fun k _ => degreeOf_consistencyFactor (F := F) C k v))
  simp only [Finset.sum_add_distrib] at hp
  have hi := sum_inputWeight_le C v
  have hr : (∑ k ∈ range C.size, refWeight (C.gates.getD k (.const false)) v) ≤ 2 := by
    rw [sum_refWeight]
    cases v with
    | inl i => exact Nat.zero_le 2
    | inr j => exact hC.fanout_le j
  have hs : (∑ k ∈ range C.size, if v = Sum.inr k then 1 else 0) ≤ 1 := by
    cases v with
    | inl i => simp
    | inr j => simp only [Sum.inr.injEq, sum_ite_eq, mem_range]; split <;> omega
  have ho : (X (.inr (C.size - 1)) : MvPolynomial (ℕ ⊕ ℕ) F).degreeOf v ≤ 1 := by
    rw [degreeOf_X]
    split <;> omega
  change _ ≤ _ at hf
  unfold routedArith
  omega
end MIPRE.SAT.Circuit
