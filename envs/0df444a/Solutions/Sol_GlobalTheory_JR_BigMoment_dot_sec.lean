-- Prove2me | solution 1 for GlobalTheory.JR.BigMoment.dot_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:32.738158+00:00
-- url     : https://prove2.me/submissions/e88d26a8-522b-4e3f-b311-2fc84d2390fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorsMatchAtOfOneLtNormFirstMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.BigMoment
namespace GlobalTheory.JR.BigMoment
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by
  simp [sec, dotProduct, Fin.sum_univ_succ]
end GlobalTheory.JR.BigMoment
