-- Prove2me | solution 1 for GlobalTheory.T.heisenbergInvariant_factors_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:33.995327+00:00
-- url     : https://prove2.me/submissions/5385e262-bc7c-4b6c-8e3e-a2e4ee70a9fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeisenbergInvariantFactorsContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeisenbergInvariantFactorsContractionStatement
import Theorems.Thm_GlobalTheory_LocFlat_contrFactor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.LocFlat.ContrFactor := by
  first | exact @GlobalTheory.LocFlat.contrFactor | exact GlobalTheory.LocFlat.contrFactor | (intros; apply GlobalTheory.LocFlat.contrFactor <;> assumption)
end _root_.GlobalTheory.T
