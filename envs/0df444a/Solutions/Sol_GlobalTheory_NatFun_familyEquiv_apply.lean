-- Prove2me | solution 1 for GlobalTheory.NatFun.familyEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:52.933293+00:00
-- url     : https://prove2.me/submissions/491efaa0-c8bb-448c-9ba7-4f3d6656fd87

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
theorem _root_.solution (h𝒯 : 𝒯.StableAway) (hX : HasCharts 𝒯 X) (s : Γ(X.left, ⊤))
    (A : Type) [CommRing A] [Algebra k A] (hA : 𝒯 A) (x : sp A ⟶ X) :
    (familyEquiv h𝒯 hX s).app A hA x = value x s := rfl
end GlobalTheory.NatFun
