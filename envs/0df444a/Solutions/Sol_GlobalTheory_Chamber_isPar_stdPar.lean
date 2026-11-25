-- Prove2me | solution 1 for GlobalTheory.Chamber.isPar_stdPar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:11.31411+00:00
-- url     : https://prove2.me/submissions/48de89c0-436a-4b5d-85df-2aed917c0133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_InverseChamberMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace ContDiff Classical
open GlobalTheory GlobalTheory.Chamber
variable {k : ℕ}
namespace GlobalTheory.Chamber
theorem _root_.solution (J : Finset (Fin k)) : IsPar (stdPar J) := by
  refine ⟨fun h => ?_, fun u hu u' hu' => ?_⟩
  · obtain ⟨j, -, e⟩ := mem_image.1 h
    simpa [stdVec] using congrFun e j
  · obtain ⟨j, -, rfl⟩ := mem_image.1 hu
    obtain ⟨j', -, rfl⟩ := mem_image.1 hu'
    have key : ∀ a b : Fin k, a ≤ b → Below (stdVec a) (stdVec b) := fun a b h i hi => by
      have : i ≤ a := by by_contra e; exact hi (if_neg e)
      simp [stdVec, this, this.trans h]
    exact (le_total j j').imp (key _ _) (key _ _)
end GlobalTheory.Chamber
