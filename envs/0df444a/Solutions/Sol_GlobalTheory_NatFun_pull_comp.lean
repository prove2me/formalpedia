-- Prove2me | solution 1 for GlobalTheory.NatFun.pull_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:14.210972+00:00
-- url     : https://prove2.me/submissions/860c58d9-e788-4aec-a375-9c17652bc3b5

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
namespace GlobalTheory.NatFun
theorem _root_.solution {X Y Z : Over (Spec (CommRingCat.of k))} (m : Z ⟶ Y) (n : Y ⟶ X)
    (s : Γ(X.left, ⊤)) : pull (m ≫ n) s = pull m (pull n s) := rfl
end GlobalTheory.NatFun
