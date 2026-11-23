-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.gr_cst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:20.642612+00:00
-- url     : https://prove2.me/submissions/6ba3870e-76c0-47e4-8751-fd5abc2b4645

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_appLE

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
theorem _root_.solution (f : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of R)) (z : Z) (V : X.Opens) (h : f z ∈ V)
    (r : R) : gr f z V h (cst p V r) = cstS (f ≫ p) z r :=
  gr_appLE f p z ⊤ V le_top h _
end GlobalTheory.SmallExtLift
