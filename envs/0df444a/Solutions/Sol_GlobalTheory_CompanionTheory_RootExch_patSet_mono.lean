-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.patSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:39.063187+00:00
-- url     : https://prove2.me/submissions/cf9493c0-8762-42ca-a7f1-8434cf001df1

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
theorem _root_.solution {Φ Ψ : ι → ι → Prop} (h : ∀ i j, Φ i j → Ψ i j) {g : GL ι K} (hg : g ∈ patSet K Φ) :
    g ∈ patSet K Ψ := fun i j => ⟨(hg i j).1, fun hij hn => (hg i j).2 hij fun hΦ => hn (h i j hΦ)⟩
end GlobalTheory.CompanionTheory.RootExch
