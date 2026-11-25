-- Prove2me | solution 1 for GlobalTheory.NatFun.spMap_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:09:04.175687+00:00
-- url     : https://prove2.me/submissions/e6a9a08a-d0da-4f2a-827c-5988ece2ec6c

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
variable {X : Over (Spec (CommRingCat.of k))}
variable {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
namespace GlobalTheory.NatFun
theorem _root_.solution : spMap (AlgHom.id k A) = 𝟙 (sp (R₀ := k) A) :=
  Over.OverMorphism.ext (Spec.map_id _)
end GlobalTheory.NatFun
