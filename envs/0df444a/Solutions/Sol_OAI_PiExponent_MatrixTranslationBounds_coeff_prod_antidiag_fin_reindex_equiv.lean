-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_equiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:45:18.507962+00:00
-- url     : https://prove2.me/submissions/1542988c-a65a-4a22-a56f-4399bf4fe5d9

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-!
The antidiagonal condition bounds each coordinate by the total weight k.
The inverse uses the finite-type finitely-supported function equivalence.
-/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ e :
      {l : ι →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k} ≃
      {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k},
      ∀ l i, ((e l).1 i).val = l.1 i := by
  classical
  let A := {l : ι →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k}
  let B := {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k}
  let e : A ≃ B :=
    { toFun := fun l =>
        ⟨fun i =>
          ⟨l.1 i, by
            have hsum : (∑ j : ι, l.1 j) = k := by
              have h := (Finset.mem_finsuppAntidiag).1 l.2
              exact h.1
            have hle : l.1 i ≤ k := by
              calc
                l.1 i ≤ ∑ j : ι, l.1 j :=
                  Finset.single_le_sum (fun j hj => Nat.zero_le (l.1 j)) (Finset.mem_univ i)
                _ = k := hsum
            exact Nat.lt_succ_of_le hle⟩,
          by
            have hsum : (∑ j : ι, l.1 j) = k := by
              have h := (Finset.mem_finsuppAntidiag).1 l.2
              exact h.1
            simpa using hsum⟩
      invFun := fun f =>
        ⟨Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val), by
          apply (Finset.mem_finsuppAntidiag).2
          constructor
          · change (∑ i : ι, (Finsupp.equivFunOnFinite.symm (fun i => (f.1 i).val)) i) = k
            simpa using f.2
          · simp⟩
      left_inv := by
        intro l
        apply Subtype.ext
        ext i
        simp
      right_inv := by
        intro f
        apply Subtype.ext
        ext i
        simp }
  refine ⟨e, ?_⟩
  intro l i
  rfl
