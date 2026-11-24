-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenPi.coords_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:55.010411+00:00
-- url     : https://prove2.me/submissions/982a9236-1c51-494d-8497-cf26fca9243d

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
theorem _root_.solution (u : ∀ i, ℍ[R i, a i, b i]) : coords (glue u) = fun k i => coords (u i) k := by
  funext k i
  fin_cases k <;> rfl
end GlobalTheory.QSA.TraceOpenPi
