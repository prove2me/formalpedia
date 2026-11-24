-- Prove2me | solution 1 for GlobalTheory.WeilM.IsContOn.of_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:15:44.410737+00:00
-- url     : https://prove2.me/submissions/5bb957b0-c24c-4463-893d-ed4bc4c63d6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]
namespace GlobalTheory.WeilM
namespace IsContOn
theorem _root_.solution [TopologicalSpace G] {C : TestClass R} {om : G →* Module.End ℂ ((κ → R) → ℂ)}
    (h : ∀ φ ∈ C.sp κ, IsLocallyConstant fun g => om g φ) : IsContOn C om :=
  fun l _ φ hφ => ((h φ hφ).comp l).continuous
end IsContOn
end GlobalTheory.WeilM
