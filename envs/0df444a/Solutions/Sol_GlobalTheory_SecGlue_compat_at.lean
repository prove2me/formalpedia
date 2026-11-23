-- Prove2me | solution 1 for GlobalTheory.SecGlue.compat_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:06.857739+00:00
-- url     : https://prove2.me/submissions/5c8096d5-8b15-444c-9e6e-6c00607564cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}
namespace GlobalTheory.SecGlue
theorem _root_.solution {φ : K → (X ⟶ A)} (r : Z ⟶ X) (z : Z) {j j' : K → L.ι}
    (f : Γ(X, LB.wchart L φ j)) (f' : Γ(X, LB.wchart L φ j'))
    (hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j')
    (h : gs r z _ f = (trF φ ε r z j j').val * gs r z _ f') :
    gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((X.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') (((LB.LinComb L φ ε).g j j').val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom f') := by
  refine (gs_res r z _ hm _).trans (h.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))).symm)
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (gm_linComb L φ ε r z j j' hm.1 hm.2))
end GlobalTheory.SecGlue
