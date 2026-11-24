-- Prove2me | solution 1 for GlobalTheory.T.quaternionNormOneTraceOpen_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:21:12.144875+00:00
-- url     : https://prove2.me/submissions/b37d80c8-4317-4fe1-8592-11b986a56315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPiStatement
import Theorems.Thm_GlobalTheory_QSA_traceOpen_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i), (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  first | exact @GlobalTheory.QSA.traceOpen_pi | exact GlobalTheory.QSA.traceOpen_pi | (intros; apply GlobalTheory.QSA.traceOpen_pi <;> assumption)
end _root_.GlobalTheory.T
