-- Prove2me | solution 1 for GlobalTheory.UU.existsUnique_torusCompat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:00:53.001529+00:00
-- url     : https://prove2.me/submissions/d5dc3537-c734-4629-acc0-80aae80fe2a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat

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
theorem _root_.solution {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsPullback F G'.hom G.hom f) (i : splitTorus S X ⟶ G) :
    ∃! i' : splitTorus S' X ⟶ G', TorusCompat f F i' i := by
  have hw : (bcMap f X ≫ i.left) ≫ G.hom = (splitTorus S' X).hom ≫ f := by
    rw [Category.assoc, Over.w i, bcMap_hom]
  refine ⟨Over.homMk (hF.lift _ _ hw) (hF.lift_snd _ _ hw), ?_, ?_⟩
  · dsimp only
    rw [torusCompat_iff]
    exact (hF.lift_fst _ _ hw).symm
  · intro j hj
    rw [torusCompat_iff] at hj
    ext
    apply hF.hom_ext
    · rw [← hj]
      simp
    · simp
end GlobalTheory.UU
