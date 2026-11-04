-- Prove2me | solution 1 for MarkovEntanglementExact.inducedMatrix_isTransitionMatrix
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:34:16.918803+00:00
-- url     : https://prove2.me/submissions/321bb879-6383-4714-8348-1a5a30e1d309

import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsFeasibleKernel
import Definitions.Def_MarkovEntanglementExact_IsFeasiblePolicy
import Definitions.Def_MarkovEntanglementExact_inducedMatrix

open scoped BigOperators
open MarkovEntanglement MarkovEntanglementExact

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    {AA : SA → Type*} {AB : SB → Type*} [∀ s, Fintype (AA s)] [∀ s, Fintype (AB s)]
    (kernel : (s : SA × SB) → AA s.1 × AB s.2 → SA × SB → ℝ)
    (hkernel : IsFeasibleKernel kernel)
    (π : (s : SA × SB) → AA s.1 × AB s.2 → ℝ)
    (hπ : IsFeasiblePolicy π) :
    IsTransitionMatrix (inducedMatrix kernel π) := by
  classical
  constructor
  · intro p q
    exact mul_nonneg (hkernel.1 _ _ _) (hπ.1 _ _)
  · intro p
    let e : ((Σ s, AA s) × (Σ s, AB s)) ≃
        (Σ s : SA × SB, AA s.1 × AB s.2) :=
      { toFun := fun q => ⟨(q.1.1, q.2.1), (q.1.2, q.2.2)⟩
        invFun := fun q => (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
        left_inv := by rintro ⟨⟨sA, aA⟩, ⟨sB, aB⟩⟩; rfl
        right_inv := by rintro ⟨⟨sA, sB⟩, ⟨aA, aB⟩⟩; rfl }
    change (∑ q, inducedMatrix kernel π p q) = 1
    calc
      (∑ q, inducedMatrix kernel π p q) =
          ∑ q : Σ s : SA × SB, AA s.1 × AB s.2,
            kernel (p.1.1, p.2.1) (p.1.2, p.2.2) q.1 * π q.1 q.2 := by
        exact Fintype.sum_equiv e _ _ (fun q => rfl)
      _ = 1 := by
        rw [Fintype.sum_sigma]
        simp_rw [← Finset.mul_sum, hπ.2, mul_one]
        exact hkernel.2 _ _

#print axioms solution
