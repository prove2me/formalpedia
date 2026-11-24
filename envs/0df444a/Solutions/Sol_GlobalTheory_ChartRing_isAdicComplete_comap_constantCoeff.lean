-- Prove2me | solution 1 for GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:49.890048+00:00
-- url     : https://prove2.me/submissions/f0de0d63-b3f7-4096-a815-d818f5065782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_isHausdorff_comap_constantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_isPrecomplete_comap_constantCoeff

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
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace GlobalTheory.ChartRing
theorem _root_.solution [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ :=
  { isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }
end GlobalTheory.ChartRing
