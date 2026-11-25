-- Prove2me | solution 1 for GlobalTheory.T.eventually_haar_det_eq_one_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:44.032717+00:00
-- url     : https://prove2.me/submissions/9e4ff12d-a9d7-44df-bfa1-262fd5cded28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyHaarDetEqOneNearOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyHaarDetEqOneNearOneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalModule_distribHaarChar_det_eventually_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k), MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | exact GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one <;> assumption)
end _root_.GlobalTheory.T
