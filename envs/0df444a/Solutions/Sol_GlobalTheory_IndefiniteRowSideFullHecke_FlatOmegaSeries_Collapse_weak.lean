-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries.Collapse.weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:56.165534+00:00
-- url     : https://prove2.me/submissions/fa38ec5a-3d21-4847-a4ba-9e2a0eef1ffb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
namespace Collapse
theorem _root_.solution (H : Collapse) : CollapseWeak := by
  intro k _ _ _ _ _ _ n _ _ c hc ν μX μG hν hX hG J ho hcp bas n' _ _ ψ hψ hψ1 μ lam Φ h1 h2
  obtain ⟨κ, hκ, H'⟩ := H k n c hc ν μX μG hν hX hG J ho hcp bas
  exact ⟨κ, hκ, H' n' ψ hψ hψ1 μ lam Φ h1 h2⟩
end Collapse
end GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
