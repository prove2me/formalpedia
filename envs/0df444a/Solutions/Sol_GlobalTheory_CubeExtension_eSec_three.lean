-- Prove2me | solution 1 for GlobalTheory.CubeExtension.eSec_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:20.309561+00:00
-- url     : https://prove2.me/submissions/eadb3766-f87d-42a4-8551-d055dc614d59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CubeExtension
variable {S : Scheme.{0}}
variable (G : Over S) [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.CubeExtension
theorem _root_.solution :
    eSec (G3 G) = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) (1 : 𝟙_ (Over S) ⟶ G))).left := by
  unfold eSec
  congr 1
  ext <;> simp [Hom.one_def]
end GlobalTheory.CubeExtension
