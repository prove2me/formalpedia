-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.complete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:19.309956+00:00
-- url     : https://prove2.me/submissions/d3dff4b1-0ae4-4f1d-97ba-078d502e754c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by
  have h := AdicCompletion.isAdicComplete (M := V) (Submodule.fg_span_singleton x)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {x}) V),
    Ideal.map_span, Set.image_singleton] at h
  exact h
end GlobalTheory.PerfectCompletion
