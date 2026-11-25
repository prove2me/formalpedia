-- Prove2me | solution 1 for GlobalTheory.TorusGrading.top_le_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:08:30.013105+00:00
-- url     : https://prove2.me/submissions/713d3413-41eb-4202-9a24-921dd4da2d08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorusGrading
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
namespace GlobalTheory.TorusGrading
theorem _root_.solution
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (h : ⊤ ≤ g.left ⁻¹ᵁ V) : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V := by
  have e : (t ≫ i) * g = lift t g ≫ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G) := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  rw [e, Over.comp_left, Scheme.Hom.comp_preimage]
  refine le_trans ?_ ((lift t g).left.preimage_mono hst)
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, lift_snd]
  exact h
end GlobalTheory.TorusGrading
