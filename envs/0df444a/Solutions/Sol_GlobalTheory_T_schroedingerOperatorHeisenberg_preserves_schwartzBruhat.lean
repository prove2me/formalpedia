-- Prove2me | solution 1 for GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:48.303238+00:00
-- url     : https://prove2.me/submissions/8144a182-8800-4d3c-9de9-f3d18fe124b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzB
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
import Theorems.Thm_GlobalTheory_Adopt_schroedingerOperatorHeisenberg_preserves_schwartzBruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat | exact GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat | (intros; apply GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat <;> assumption)
end _root_.GlobalTheory.T
