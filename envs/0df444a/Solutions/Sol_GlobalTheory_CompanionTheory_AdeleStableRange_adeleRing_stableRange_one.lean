-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleStableRange.adeleRing_stableRange_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:20.197823+00:00
-- url     : https://prove2.me/submissions/2edf017a-a908-4b44-ac5e-912898024cc6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdeleRingStableRangeOne
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_finite_part
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleStableRange_infinite_part

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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : AdeleRing (𝓞 F) F),
    IsCoprime a b → ∃ t, IsUnit (a + t * b) := by
  intro F _ _ a b hab
  obtain ⟨x, y, hxy⟩ := hab
  obtain ⟨t₁, u₁⟩ := infinite_part F a.1 b.1 ⟨x.1, y.1, congrArg Prod.fst hxy⟩
  obtain ⟨t₂, u₂⟩ := finite_part (𝓞 F) F a.2 b.2 ⟨x.2, y.2, congrArg Prod.snd hxy⟩
  exact ⟨(t₁, t₂), Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩
end GlobalTheory.CompanionTheory.AdeleStableRange
