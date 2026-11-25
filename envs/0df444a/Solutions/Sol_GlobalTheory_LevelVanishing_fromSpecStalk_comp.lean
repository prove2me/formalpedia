-- Prove2me | solution 1 for GlobalTheory.LevelVanishing.fromSpecStalk_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:29.124307+00:00
-- url     : https://prove2.me/submissions/925a0d62-32e7-471a-a28e-729b60125914

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FromSpecStalkComp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv


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
open GlobalTheory GlobalTheory.LevelVanishing
namespace GlobalTheory.LevelVanishing
theorem _root_.solution {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
end GlobalTheory.LevelVanishing
