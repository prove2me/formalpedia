-- Prove2me | solution 1 for GlobalTheory.JR.EtQuot.idem_eq_one_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:35.95815+00:00
-- url     : https://prove2.me/submissions/16eb529c-6f2c-4302-a058-610408554dea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot
namespace GlobalTheory.JR.EtQuot
theorem _root_.solution {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (hu : IsUnit e) : e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (u : K) = u * u * ↑u⁻¹ := by simp
    _ = u * ↑u⁻¹ := by rw [he.eq]
    _ = 1 := by simp
end GlobalTheory.JR.EtQuot
