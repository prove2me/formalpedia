-- Prove2me | solution 1 for GlobalTheory.LatticePartition.bump_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:38:51.674114+00:00
-- url     : https://prove2.me/submissions/21482b22-65f3-4a1c-af5b-bd5d924b7c6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
noncomputable section
open GlobalTheory GlobalTheory.LatticePartition
namespace GlobalTheory.LatticePartition
theorem _root_.solution : ContDiff ℝ ∞ bump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff
end GlobalTheory.LatticePartition
