-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.act_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:01:14.937943+00:00
-- url     : https://prove2.me/submissions/2e431e9d-b381-453d-b9a2-cf7472bd1c75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp
end GlobalTheory.JR.LinDesc
