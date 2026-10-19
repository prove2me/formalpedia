-- Prove2me | solution 1 for MIPRE.LowDegree.exists_zero_basis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:28.931409+00:00
-- url     : https://prove2.me/submissions/818538d4-977b-4385-bdfa-465b266f51d5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/ZeroBasis.lean (solution of MIPRE.LowDegree.exists_zero_basis);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] {m : ℕ}
theorem _root_.solution (f : MvPolynomial (Fin m) F) {d : ℕ}
    (hd : ∀ i, f.degreeOf i ≤ d) (hf : ∀ y : Fin m → Bool, eval (pt y) f = 0) :
    ∃ c : Fin m → MvPolynomial (Fin m) F,
      f = ∑ i, c i * cubeZero i ∧ ∀ i j, (c i).degreeOf j ≤ d := by
  classical
  obtain ⟨c, r, hfr, hc, _, hr⟩ := exists_cube_remainder f univ
  have heval (y : Fin m → Bool) : eval (pt y) r = 0 := by
    have h := hf y
    rw [hfr, map_add, map_sum] at h
    simpa using h
  have hz : r = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset r (fun _ => {0, 1})
    · intro i
      have := hr i (mem_univ i)
      simpa using Nat.lt_succ_of_le this
    · intro x hx
      let y : Fin m → Bool := fun i => decide (x i = 1)
      have hxy : pt y = x := by
        funext i
        have h := hx i
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h <;> simp [pt, y, ofBool, h]
      simpa [hxy] using heval y
  exact ⟨c, by simpa [hz] using hfr, fun i j => (hc i j).trans (hd j)⟩
end MIPRE.LowDegree
