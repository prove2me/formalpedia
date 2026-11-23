-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.pow_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:50.242464+00:00
-- url     : https://prove2.me/submissions/1717d094-ad71-4bd6-8163-c68a2587b02e

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
variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by
  have := (frobeniusEquiv V l).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this
end GlobalTheory.PerfectCompletion
