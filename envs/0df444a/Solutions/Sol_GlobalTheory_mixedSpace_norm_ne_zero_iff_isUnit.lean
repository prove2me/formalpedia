-- Prove2me | solution 1 for GlobalTheory.mixedSpace_norm_ne_zero_iff_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:15.575403+00:00
-- url     : https://prove2.me/submissions/f20b853b-7309-4d32-9ca7-a738d9986b21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K]
    (x : mixedSpace K) : mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  rw [mixedEmbedding.norm_ne_zero_iff, Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  constructor
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · have := h w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
    · have := h w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
  · rintro ⟨h1, h2⟩ w
    rcases w.isReal_or_isComplex with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]
      exact norm_ne_zero_iff.mpr (h1 _).ne_zero
    · rw [normAtPlace_apply_of_isComplex hw]
      exact norm_ne_zero_iff.mpr (h2 _).ne_zero
end GlobalTheory
