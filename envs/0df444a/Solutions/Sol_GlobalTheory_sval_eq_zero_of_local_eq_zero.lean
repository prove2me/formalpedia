-- Prove2me | solution 1 for GlobalTheory.sval_eq_zero_of_local_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:54.839684+00:00
-- url     : https://prove2.me/submissions/f3e66dc7-2640-48c0-bb1b-2aa27217282b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfSvalWhiskerRightEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PullbackSectionFamilyNeZeroIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, d.f j = 0) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) : sval d r z J = 0 := by
  have e : gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) 0 = 0 := by
    rw [gs_eq r z _ (hJ.mem φ r), map_zero, map_zero]
  exact (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans e
end GlobalTheory
