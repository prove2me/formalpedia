-- Prove2me | solution 1 for GlobalTheory.algebraMap_padicInt_finExt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:22.316802+00:00
-- url     : https://prove2.me/submissions/0f495ad3-c14c-48cd-9d3c-f81156e652fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective

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
    Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
end GlobalTheory
