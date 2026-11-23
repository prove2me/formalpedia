-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:29.688286+00:00
-- url     : https://prove2.me/submissions/17e2c5b2-150c-4906-99be-3b91dee90dfd

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
theorem _root_.solution {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ x (hx : (𝟙 X : X ⟶ X) x ∈ V), gr (𝟙 X) x V hx a = gr (𝟙 X) x V hx b) : a = b :=
  TopCat.Presheaf.section_ext X.sheaf V _ _ h
end GlobalTheory.SmallExtLift
