-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleStableRange.infinite_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:31.738897+00:00
-- url     : https://prove2.me/submissions/939f9e27-ae03-459c-ac15-df05d81421db

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_local_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleStableRange
namespace GlobalTheory.CompanionTheory.AdeleStableRange
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (a b : InfiniteAdeleRing K)
    (hab : IsCoprime a b) : ∃ t : InfiniteAdeleRing K, IsUnit (a + t * b) := by
  obtain ⟨x, y, hxy⟩ := hab
  have hloc : ∀ v : InfinitePlace K, x v * a v + y v * b v = 1 := fun v =>
    congrArg (fun z : InfiniteAdeleRing K => z v) hxy
  choose t ht using fun v : InfinitePlace K => local_field (a v) (b v) (x v) (y v) (hloc v)
  exact ⟨t, Pi.isUnit_iff.2 ht⟩
end GlobalTheory.CompanionTheory.AdeleStableRange
