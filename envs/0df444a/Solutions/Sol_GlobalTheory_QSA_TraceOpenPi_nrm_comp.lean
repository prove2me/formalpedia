-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenPi.nrm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:58.339352+00:00
-- url     : https://prove2.me/submissions/c9064ba3-8aee-45d8-81d2-637077e8787e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA
open GlobalTheory.QSA.TraceOpenPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}
namespace GlobalTheory.QSA.TraceOpenPi
theorem _root_.solution (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by
  simp [nrm, comp]
end GlobalTheory.QSA.TraceOpenPi
