-- Prove2me | solution 1 for GlobalTheory.SecPow.basicOpen_rs_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:23.276826+00:00
-- url     : https://prove2.me/submissions/c592a833-788e-4e24-ab53-6385c1326eb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowSection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.SecPow
variable {X X' : Scheme.{0}}
namespace GlobalTheory.SecPow
theorem _root_.solution {H : LB X} (s : LB.Sec H) (i : H.ι) {V : X.Opens} (h : V ≤ H.U i) :
    X.basicOpen (rs X h (s.f i)) = V ⊓ nonzeroLocus s := by
  apply le_antisymm
  · refine le_inf (X.basicOpen_le _) ?_
    erw [Scheme.basicOpen_res]
    exact inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) i)
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s i (O := V ⊓ nonzeroLocus s)
      (inf_le_left.trans h) inf_le_right
    rw [← rs_rs h inf_le_left] at hu
    have e := X.basicOpen_of_isUnit hu
    erw [Scheme.basicOpen_res] at e
    exact e.ge.trans inf_le_right
end GlobalTheory.SecPow
