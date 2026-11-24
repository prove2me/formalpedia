-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.nz_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:08.616152+00:00
-- url     : https://prove2.me/submissions/e651258f-0c48-46fe-8cc1-5799e03d7a56

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
theorem _root_.solution {Φ : ι → ι → Prop} {g : GL ι K} (hg : g ∈ patSet K Φ) {i j : ι}
    (h : (g : Matrix ι ι K) i j ≠ 0) : i = j ∨ Φ i j := by
  by_contra hc
  push_neg at hc
  exact h ((hg i j).2 hc.1 hc.2)
end GlobalTheory.CompanionTheory.RootExch
