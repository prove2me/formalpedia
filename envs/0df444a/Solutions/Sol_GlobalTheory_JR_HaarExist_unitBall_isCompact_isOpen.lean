-- Prove2me | solution 1 for GlobalTheory.JR.HaarExist.unitBall_isCompact_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:59:43.567372+00:00
-- url     : https://prove2.me/submissions/e5c86c16-3a62-4775-a259-8f70cb23b0d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyJacquetRallisHaarMeasuresForallSize

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HaarExist
variable (r : ℕ)
namespace GlobalTheory.JR.HaarExist
theorem _root_.solution (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] :
    IsCompact (Metric.closedBall (0 : K) 1) ∧ IsOpen (Metric.closedBall (0 : K) 1) ∧
      (Metric.closedBall (0 : K) 1).Nonempty := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ⟨isCompact_closedBall _ _, IsUltrametricDist.isOpen_closedBall _ one_ne_zero, 0, by simp⟩
end GlobalTheory.JR.HaarExist
