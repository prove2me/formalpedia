-- Prove2me | solution 1 for GlobalTheory.LocFlat.symCollapse_of_allPositions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:30.683825+00:00
-- url     : https://prove2.me/submissions/9bbbe354-b12a-48c7-9594-05880b4fdcde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymCollapseOfAllPositions
import Theorems.Thm_GlobalTheory_SymChain_pattern_iter
import Theorems.Thm_GlobalTheory_T_flatColumnIndicator_pure_at_symmetricPosition
import Theorems.Thm_GlobalTheory_T_flatColumnSupport_of_oneIndexAt_symPosition
import Theorems.Thm_GlobalTheory_T_flatRowIndicator_of_symLevelExchange
import Theorems.Thm_GlobalTheory_T_symLevel_doubleStep_of_flatColumn_flatRow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : AllPositions → GlobalTheory.LocFlat.SymCollapse := by
  intro hA k _ _ _ _ _ _ ν hν s κ S t _ _
  obtain ⟨hO, hE⟩ := hA k ν hν s κ S t
  have hP : S.Pattern t := GlobalTheory.SymChain.pattern_iter k s κ S t
  have hC := GlobalTheory.T.flatColumnIndicator_pure_at_symmetricPosition k ν hν s κ S t hP hE
  have hR := GlobalTheory.T.flatRowIndicator_of_symLevelExchange k ν hν s κ S t hP hE
  exact ⟨GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition k ν hν s κ S t hO, hC, hR, GlobalTheory.T.symLevel_doubleStep_of_flatColumn_flatRow k ν hν s κ S t hP hO hC hR⟩
end GlobalTheory.LocFlat
