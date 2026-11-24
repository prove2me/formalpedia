-- Prove2me | solution 1 for GlobalTheory.DVRQuotCount.irreducible_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:36.328347+00:00
-- url     : https://prove2.me/submissions/cea8cc68-e37a-48b3-86fb-b1e0e2c6ca14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open GlobalTheory GlobalTheory.DVRQuotCount
open scoped TensorProduct DirectSum
namespace GlobalTheory.DVRQuotCount
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p t : O}
    (hp : Irreducible p) (ht : t ≠ 0) (htu : ¬ IsUnit t) : p ∣ t := by
  obtain ⟨q, hq, hqt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht
  exact (IsDiscreteValuationRing.associated_of_irreducible O hp hq).dvd.trans hqt
end GlobalTheory.DVRQuotCount
