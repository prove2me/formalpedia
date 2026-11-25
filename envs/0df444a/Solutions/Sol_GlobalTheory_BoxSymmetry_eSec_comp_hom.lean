-- Prove2me | solution 1 for GlobalTheory.BoxSymmetry.eSec_comp_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:36:48.054343+00:00
-- url     : https://prove2.me/submissions/dc641ad6-686e-4f85-a818-5a00cdb52ff3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymmetry
variable {S : Scheme.{0}}
namespace GlobalTheory.BoxSymmetry
theorem _root_.solution {G' G : Over S} [GrpObj G'] [GrpObj G] (f : G' ⟶ G) [IsMonHom f] :
    eSec G' ≫ f.left = eSec G := by
  unfold eSec
  rw [← Over.comp_left, IsMonHom.one_hom]
end GlobalTheory.BoxSymmetry
