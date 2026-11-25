-- Prove2me | solution 1 for GlobalTheory.GenExtendNormal.unit_ext_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:58:37.458143+00:00
-- url     : https://prove2.me/submissions/4f715529-af34-4463-b9bc-898ebc02d87c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_GlobalTheory_PrimeSection_appLE_injective
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendNormal
theorem _root_.solution {H Y : Scheme.{0}} [IsIntegral H] (j : Y ⟶ H)
    [IsOpenImmersion j] [Nonempty Y] {O : H.Opens} {u v : Γ(H, O)ˣ}
    (h : ∀ y, j y ∈ O → gm j y O u = gm j y O v) : u = v := by
  have : pullU j O u = pullU j O v := unit_ext fun y hy ↦ by
    rw [gm_pull (𝟙 Y) j y O hy, gm_pull (𝟙 Y) j y O hy, Category.id_comp, h y hy]
  refine Units.ext (GlobalTheory.PrimeSection.appLE_injective j (U := O) rfl ?_)
  rw [← Scheme.Hom.app_eq_appLE]
  exact congrArg Units.val this
end GlobalTheory.GenExtendNormal
