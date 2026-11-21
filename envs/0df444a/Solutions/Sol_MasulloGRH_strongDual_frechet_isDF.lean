-- Prove2me | solution 1 for MasulloGRH.strongDual_frechet_isDF
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:27:27.303176+00:00
-- url     : https://prove2.me/submissions/32090291-72a5-4cc6-a515-b0fa6218a141

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strongDual_frechet_fundamental_bounded_seq
import Theorems.Thm_MasulloGRH_strongDual_frechet_countable_bornivorous_nhds

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    (∃ B : ℕ → Set (StrongDual ℂ E), (∀ n, Bornology.IsVonNBounded ℂ (B n)) ∧
      ∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → ∃ n, S ⊆ B n) ∧
    ∀ U : ℕ → Set (StrongDual ℂ E),
      (∀ n, U n ∈ nhds (0 : StrongDual ℂ E) ∧ IsClosed (U n) ∧ Balanced ℂ (U n) ∧ Convex ℝ (U n)) →
      (∀ S : Set (StrongDual ℂ E), Bornology.IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) →
      (⋂ n, U n) ∈ nhds (0 : StrongDual ℂ E) :=
  ⟨strongDual_frechet_fundamental_bounded_seq E hE,
    fun U hU hb => strongDual_frechet_countable_bornivorous_nhds E hE U hU hb⟩
