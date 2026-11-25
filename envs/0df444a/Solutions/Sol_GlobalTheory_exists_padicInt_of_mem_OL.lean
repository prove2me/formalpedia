-- Prove2me | solution 1 for GlobalTheory.exists_padicInt_of_mem_OL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:41:05.134905+00:00
-- url     : https://prove2.me/submissions/faa5da62-0efe-4aea-b582-01cb00f621b2

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
theorem _root_.solution {l : ℕ} [Fact l.Prime] (LL : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL) : ∃ y : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] y = x := by
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 x) := hx
  have hint' : IsIntegral ℤ_[l] x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'
end GlobalTheory
