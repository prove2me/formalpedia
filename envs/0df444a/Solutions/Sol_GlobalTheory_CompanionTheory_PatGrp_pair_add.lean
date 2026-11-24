-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.pair_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:24.9628+00:00
-- url     : https://prove2.me/submissions/2e769d84-644c-4102-8524-bb41799992e5

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
theorem _root_.solution (E : ι → ι → K) (A B : Matrix ι ι K) : pair E (A + B) = pair E A + pair E B := by
  unfold pair
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.PatGrp
