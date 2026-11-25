-- Prove2me | solution 1 for GlobalTheory.algebraMap_padicInt_OL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:37.231126+00:00
-- url     : https://prove2.me/submissions/91f47e86-5c7b-4345-b9b4-826d7e3c2bdf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective
import Theorems.Thm_GlobalTheory_algebraMap_padicInt_finExt_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b h
  exact algebraMap_padicInt_finExt_injective LL (congrArg Subtype.val h)
end GlobalTheory
