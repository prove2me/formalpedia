-- Prove2me | solution 1 for N4Code.goodWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:52.17654+00:00
-- url     : https://prove2.me/submissions/9209e3f2-aff1-4997-ad5a-8aba206ff4b4

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
import Theorems.Thm_N4Code_wordTuple_mem
import Theorems.Thm_N4Code_tupleWord_mem
import Theorems.Thm_N4Code_tupleWord_wordTuple
import Theorems.Thm_N4Code_wordTuple_tupleWord

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodWords C k).card = (GoodTuples C k).card := by
  let A := {y : Word n // y ∈ GoodWords C k}
  let B := {g : Fin 16 → Finset (Fin n) // g ∈ GoodTuples C k}
  have hA : Fintype.card A = (GoodWords C k).card := by
    change (Finset.univ : Finset A).card = (GoodWords C k).card
    rw [show (Finset.univ : Finset A) = (GoodWords C k).attach by
      ext a
      exact iff_of_true (by simp) (Finset.mem_attach (GoodWords C k) a)]
    exact Finset.card_attach
  have hB : Fintype.card B = (GoodTuples C k).card := by
    change (Finset.univ : Finset B).card = (GoodTuples C k).card
    rw [show (Finset.univ : Finset B) = (GoodTuples C k).attach by
      ext g
      exact iff_of_true (by simp) (Finset.mem_attach (GoodTuples C k) g)]
    exact Finset.card_attach
  have hEq : A ≃ B :=
    { toFun := fun y => ⟨wordTuple C y.1,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, wordTuple_mem C k y.2⟩⟩
      invFun := fun g => ⟨tupleWord C g.1, tupleWord_mem C k (Finset.mem_filter.mp g.2).2⟩
      left_inv := fun y => by
        apply Subtype.ext
        exact tupleWord_wordTuple C y.1
      right_inv := fun g => by
        apply Subtype.ext
        exact wordTuple_tupleWord C k (Finset.mem_filter.mp g.2).2 }
  rw [← hA, ← hB]
  exact Fintype.card_congr hEq
end N4Code
