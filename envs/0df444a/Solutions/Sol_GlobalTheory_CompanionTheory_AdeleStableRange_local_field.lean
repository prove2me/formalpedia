-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleStableRange.local_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:09.909004+00:00
-- url     : https://prove2.me/submissions/4e9338f5-4914-4229-82ae-2106cb2f4c68

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne

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
theorem _root_.solution {K : Type*} [Field K] (a b x y : K) (h : x * a + y * b = 1) :
    ∃ t : K, IsUnit (a + t * b) := by
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    rw [isUnit_iff_ne_zero, ha]
    rintro h0
    have hb : b = 0 := by simpa using h0
    simp [ha, hb] at h
  · exact ⟨0, by simpa [isUnit_iff_ne_zero] using ha⟩
end GlobalTheory.CompanionTheory.AdeleStableRange
