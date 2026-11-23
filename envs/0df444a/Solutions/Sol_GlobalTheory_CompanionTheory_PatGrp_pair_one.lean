-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.pair_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:33.601776+00:00
-- url     : https://prove2.me/submissions/e88b6145-44f5-4b24-ba7c-1f62c100e6f9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution (h : IsPat Φ) {E : ι → ι → K} (hE : IsPatChar Φ E) : pair E (1 : Matrix ι ι K) = 0 := by
  unfold pair
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · have hEi : E i i = 0 := by
      by_contra hne
      exact h.1 i (hE.1 i i hne)
    rw [hEi, zero_mul]
  · rw [Matrix.one_apply_ne hij, mul_zero]
end GlobalTheory.CompanionTheory.PatGrp
