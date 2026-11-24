-- Prove2me | solution 1 for GlobalTheory.AnalyticMatrixEntries.analyticAt_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:48.410525+00:00
-- url     : https://prove2.me/submissions/a5d4fb46-a483-4eab-8388-d66f114b8f5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticMatrixEntries
universe u_1 u_2
namespace GlobalTheory.AnalyticMatrixEntries
theorem _root_.solution {X : Type u_1} {E : Type u_2} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} (b : Module.Basis ι ℂ E) {A : X → E →L[ℂ] E} {a : X}
    (hA : AnalyticAt ℂ A a) (i j : ι) :
    AnalyticAt ℂ (fun z : X ↦ b.repr (A z (b j)) i) a := by
  let L : (E →L[ℂ] E) →L[ℂ] ℂ :=
    (LinearMap.toContinuousLinearMap (b.coord i)).comp (ContinuousLinearMap.apply ℂ E (b j))
  have h := (L.analyticAt (A a)).comp hA
  convert h using 1
  funext z
  simp [L, Module.Basis.coord_apply]
end GlobalTheory.AnalyticMatrixEntries
