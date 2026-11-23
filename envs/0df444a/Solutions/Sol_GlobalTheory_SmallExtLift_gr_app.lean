-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_app
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:43.71828+00:00
-- url     : https://prove2.me/submissions/afc2b94f-eacf-4073-9f34-aea8b92671e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gr f z (g ⁻¹ᵁ U) h ((g.app U).hom a) = gr (f ≫ g) z U h a := rfl
end GlobalTheory.SmallExtLift
