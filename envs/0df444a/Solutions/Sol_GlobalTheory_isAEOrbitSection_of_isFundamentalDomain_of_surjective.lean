-- Prove2me | solution 1 for GlobalTheory.isAEOrbitSection_of_isFundamentalDomain_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:51.224561+00:00
-- url     : https://prove2.me/submissions/b6d9a52d-1264-4c3d-9ec9-b37a0405c741

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory
theorem _root_.solution [Countable G] {Q : Type*} [Group Q]
    [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ) (hact : ∀ g (x : X), φ g • x = g • x)
    {D : Set X} (hD : IsFundamentalDomain Q D μ) : IsAEOrbitSection G D μ := by
  have : Countable Q := hφ.countable
  refine (isAEOrbitSection_of_isFundamentalDomain hD).of_sameOrbits (fun q x => ?_)
    fun g x => ⟨φ g, hact g x⟩
  obtain ⟨g, rfl⟩ := hφ q
  exact ⟨g, (hact g x).symm⟩
end GlobalTheory
