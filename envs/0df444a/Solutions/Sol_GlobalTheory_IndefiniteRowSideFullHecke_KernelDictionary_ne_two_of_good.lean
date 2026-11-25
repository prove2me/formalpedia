-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary.ne_two_of_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:25.751292+00:00
-- url     : https://prove2.me/submissions/5fb5ab58-cfc5-4008-ac8f-f9f464e0dc5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
theorem _root_.solution {K LL : FinExt l} (h : Good K 1 LL) : l ≠ 2 := fun h2 => by
  have := h.2.1 h2
  omega
end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
