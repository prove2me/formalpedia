-- Prove2me | solution 1 for GlobalTheory.T.not_mem_Lp_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:32.381746+00:00
-- url     : https://prove2.me/submissions/5b0a37e7-60fb-4638-9f6d-15bdb12cabb2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowth
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NotMemLpOfGrowthStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_mul_rpow_lt_one_of_memLp_geometric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
end _root_.GlobalTheory.T
