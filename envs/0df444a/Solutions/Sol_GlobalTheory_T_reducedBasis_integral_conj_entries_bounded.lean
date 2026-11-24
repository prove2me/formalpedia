-- Prove2me | solution 1 for GlobalTheory.T.reducedBasis_integral_conj_entries_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:13.887641+00:00
-- url     : https://prove2.me/submissions/17762e06-0a5e-4157-a1ce-bcc0e89a98c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBoundedStatement
import Theorems.Thm_GlobalTheory_ReducedBasisBound_integral_conj_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.ReducedBasisBound.integral_conj_bounded | exact GlobalTheory.ReducedBasisBound.integral_conj_bounded | (intros; apply GlobalTheory.ReducedBasisBound.integral_conj_bounded <;> assumption)
end _root_.GlobalTheory.T
