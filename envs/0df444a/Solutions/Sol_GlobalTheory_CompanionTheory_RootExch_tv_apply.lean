-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.tv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:39.873504+00:00
-- url     : https://prove2.me/submissions/cf4b0ec3-8d42-46ea-89f4-8cd94c31abc1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution (r t : ι) (h : r ≠ t) (s : K) (i j : ι) :
    ((tv r t h s : GL ι K) : Matrix ι ι K) i j = (1 : Matrix ι ι K) i j + if i = r ∧ j = t then s else 0 := by
  change (Matrix.transvection r t s) i j = _
  simp [Matrix.transvection, Matrix.single_apply, eq_comm]
end GlobalTheory.CompanionTheory.RootExch
