-- Prove2me | solution 1 for MIPRE.SAT.Circuit.sum_inputWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:23.613099+00:00
-- url     : https://prove2.me/submissions/89d9b372-010d-4470-bbb1-cfe7d6f35241

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitArithmetization.lean (solution of MIPRE.SAT.Circuit.sum_inputWeight_le);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
/-- Each external input or previous input gate is used by at most one copy link. -/
theorem inputRef_injective (C : Circuit) {a b i j : ℕ}
    (ha : C.gates.getD a (.const false) = .input i)
    (hb : C.gates.getD b (.const false) = .input j)
    (he : C.inputRef a i = C.inputRef b j) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (inputRef_ne_of_lt C h ha he)
  · exact h
  · exact False.elim (inputRef_ne_of_lt C h hb he.symm)
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open MvPolynomial LowDegree Finset
variable {F : Type*} [Field F]
theorem _root_.solution (C : Circuit) (v : ℕ ⊕ ℕ) :
    ∑ k ∈ range C.size, C.inputWeight k v ≤ 1 := by
  rw [Finset.sum_le_one_iff]
  intro a b ha hb hwa hwb
  have key (k : ℕ) (hk : C.inputWeight k v ≠ 0) :
      ∃ i, C.gates.getD k (.const false) = .input i ∧ v = C.inputRef k i := by
    unfold inputWeight at hk
    split at hk <;> try contradiction
    split_ifs at hk with h
    · exact ⟨_, ‹_ = Gate.input _›, h⟩
    · contradiction
  obtain ⟨i, hi, hv⟩ := key a hwa
  obtain ⟨j, hj, hv'⟩ := key b hwb
  refine ⟨inputRef_injective C hi hj (hv.symm.trans hv'), ?_⟩
  simp only [inputWeight, hi, if_pos hv]
end MIPRE.SAT.Circuit
