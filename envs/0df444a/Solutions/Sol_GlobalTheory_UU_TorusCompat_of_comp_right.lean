-- Prove2me | solution 1 for GlobalTheory.UU.TorusCompat.of_comp_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:27.639011+00:00
-- url     : https://prove2.me/submissions/587377fe-0d01-4b5b-a463-db7224412fa4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_GlobalTheory_UU_bcMap_comp

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
noncomputable section
open GlobalTheory GlobalTheory.UU
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G'' : Over S''} {G' : Over S'} {G : Over S}
namespace GlobalTheory.UU
namespace TorusCompat
theorem _root_.solution {f' : S'' ⟶ S'} {f : S' ⟶ S} {F' : G''.left ⟶ G'.left}
    {F : G'.left ⟶ G.left} (hF : IsPullback F G'.hom G.hom f) (hF' : F' ≫ G'.hom = G''.hom ≫ f')
    {i'' : splitTorus S'' X ⟶ G''} {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G}
    (h'' : TorusCompat (f' ≫ f) (F' ≫ F) i'' i) (h : TorusCompat f F i' i) :
    TorusCompat f' F' i'' i' := by
  rw [torusCompat_iff] at h'' h ⊢
  rw [bcMap_comp] at h''
  apply hF.hom_ext
  · simp only [Category.assoc] at h'' ⊢
    rw [← h, h'']
  · simp [hF', bcMap_hom]
end TorusCompat
end GlobalTheory.UU
