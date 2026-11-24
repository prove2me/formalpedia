-- Prove2me | solution 1 for GlobalTheory.T.addHaar_proper_submodule_eq_zero_moduleTopology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:02:48.165846+00:00
-- url     : https://prove2.me/submissions/42f561de-2a82-4468-a0ae-8b1d6aad4423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddHaarProperSubmoduleEqZeroModuleTopologyStatement
import Theorems.Thm_GlobalTheory_HaarNullSub_addHaar_submodule_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ s : Submodule F V, s ≠ ⊤ → μ (s : Set V) = 0 := by
  first | exact @GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | exact GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero | (intros; apply GlobalTheory.HaarNullSub.addHaar_submodule_eq_zero <;> assumption)
end _root_.GlobalTheory.T
