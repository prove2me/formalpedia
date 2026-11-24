-- Prove2me | solution 1 for GlobalTheory.T.siegelReduced_integral_form_bounded_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:58.270623+00:00
-- url     : https://prove2.me/submissions/abaff43c-8d20-4575-a1b3-b777273dbcdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntriesStatement
import Theorems.Thm_GlobalTheory_RedBound_reduced_bound


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
theorem _root_.solution : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) → B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) → (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X → ∀ i j, |(B i j : ℝ)| ≤ C' := by
  first | exact @GlobalTheory.RedBound.reduced_bound | exact GlobalTheory.RedBound.reduced_bound | (intros; apply GlobalTheory.RedBound.reduced_bound <;> assumption)
end _root_.GlobalTheory.T
