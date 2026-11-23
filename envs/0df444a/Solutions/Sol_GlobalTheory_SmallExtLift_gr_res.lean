-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:29.593749+00:00
-- url     : https://prove2.me/submissions/589fd8c8-95d7-4326-92ba-680040abe265

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
theorem _root_.solution (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gr f y V h ((X.presheaf.map (homOfLE hle).op).hom a) = gr f y U (hle h) a := by
  have e := congrArg (fun q => q.hom a) (f.naturality (homOfLE hle).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact (congrArg (Y.presheaf.germ (f ⁻¹ᵁ V) y h).hom e).trans
    (TopCat.Presheaf.germ_res_apply Y.presheaf _ y h _)
end GlobalTheory.SmallExtLift
