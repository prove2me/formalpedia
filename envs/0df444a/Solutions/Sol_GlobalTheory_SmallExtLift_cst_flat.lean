-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.cst_flat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:19.417382+00:00
-- url     : https://prove2.me/submissions/1f28ab0e-2048-457b-bb70-3d6c62c0dd07

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
variable {R : Type} [CommRing R]
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (p : X ⟶ Spec (CommRingCat.of R))
    [Flat p] {V : X.Opens} (hV : IsAffineOpen V) : (cst p V).Flat :=
  RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
    (p.flat_appLE (isAffineOpen_top _) hV le_top)
end GlobalTheory.SmallExtLift
