-- Prove2me | solution 1 for GlobalTheory.ChartRing.evalAdic_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:05.482045+00:00
-- url     : https://prove2.me/submissions/4d74436c-240f-4bd8-b9a1-7e7d832f8b65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
namespace GlobalTheory.ChartRing
theorem _root_.solution (a : A) : evalAdic A J hs (C a) = algebraMap A S a :=
  (evalAdic A J hs).commutes a
end GlobalTheory.ChartRing
