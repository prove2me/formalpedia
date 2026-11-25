-- Prove2me | solution 1 for GlobalTheory.CubeExtension.formEq_origin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:25.389328+00:00
-- url     : https://prove2.me/submissions/857e2bf0-d7d1-417c-b2a8-4f620000d132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Theorems.Thm_GlobalTheory_CubeExtension_eSec_three
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


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
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → ((𝟙_ (Over S)).left ⟶ G.left)) PEmpty.elim
      (fun I => eSec (G3 G) ≫ thφ G (x3 G) I) thε := by
  intro U _ h
  rw [eSec_three, prod_cub]
  simp
end GlobalTheory.CubeExtension
