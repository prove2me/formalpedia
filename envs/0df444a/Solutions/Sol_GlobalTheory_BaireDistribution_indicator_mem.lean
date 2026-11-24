-- Prove2me | solution 1 for GlobalTheory.BaireDistribution.indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:00:20.807564+00:00
-- url     : https://prove2.me/submissions/1dea115e-7bc1-42ad-9e7a-fdea9b1f65f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.BaireDistribution
variable {X : Type} [TopologicalSpace X]
namespace GlobalTheory.BaireDistribution
theorem _root_.solution {C : Set X} (hC : IsClopen C) (φ : SB X) : C.indicator φ.1 ∈ SB X := by
  refine ⟨?_, φ.2.2.mono fun x hx => ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ C
    · obtain ⟨U, hU, hxU, h⟩ := φ.2.1.exists_open x
      exact ⟨C ∩ U, hC.2.inter hU, ⟨hx, hxU⟩, fun y hy => by
        rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hx, h y hy.2]⟩
    · exact ⟨Cᶜ, hC.1.isOpen_compl, hx, fun y hy => by
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · rw [Set.support_indicator] at hx
    exact hx.2
end GlobalTheory.BaireDistribution
