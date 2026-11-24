-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenPi.nrm_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:59.140995+00:00
-- url     : https://prove2.me/submissions/bbb7ade7-8c5a-4b7a-8854-df1e4704f10a

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
theorem _root_.solution (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by
  funext i
  simp [nrm, glue]
end GlobalTheory.QSA.TraceOpenPi
