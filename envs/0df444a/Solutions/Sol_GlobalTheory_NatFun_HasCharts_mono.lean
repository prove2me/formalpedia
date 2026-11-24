-- Prove2me | solution 1 for GlobalTheory.NatFun.HasCharts.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:48.199845+00:00
-- url     : https://prove2.me/submissions/cead5220-2134-4bc8-928f-c2a148288af0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)
open GlobalTheory GlobalTheory.NatFun
variable {k : Type} [CommRing k]
variable {𝒯 𝒯' : AlgClass k} {X : Over (Spec (CommRingCat.of k))}
namespace GlobalTheory.NatFun
namespace HasCharts
theorem _root_.solution (h : HasCharts 𝒯 X)
    (hle : ∀ (A : Type) [CommRing A] [Algebra k A], 𝒯 A → 𝒯' A) : HasCharts 𝒯' X := fun p => by
  obtain ⟨A, _, _, u, hA, hu⟩ := h p
  exact ⟨A, _, _, u, hle A hA, hu⟩
end HasCharts
end GlobalTheory.NatFun
