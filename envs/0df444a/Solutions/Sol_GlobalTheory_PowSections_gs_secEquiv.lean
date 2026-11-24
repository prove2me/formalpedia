-- Prove2me | solution 1 for GlobalTheory.PowSections.gs_secEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:32:21.925041+00:00
-- url     : https://prove2.me/submissions/ee3071f6-2b9e-49bf-999c-137a69d61389

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEquivPow

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
open GlobalTheory
open GlobalTheory.PowSections
variable {Y : Scheme.{0}}
namespace GlobalTheory.PowSections
theorem _root_.solution {M M' : LB Y} (σ : M'.ι ≃ M.ι) (hU : ∀ i, M'.U i = M.U (σ i))
    (hg : ∀ i j y, y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y _ (M'.g i j) = gm (𝟙 Y) y _ (M.g (σ i) (σ j))) (s : LB.Sec M) (i : M'.ι) (y : Y)
    (hy : y ∈ M'.U i) :
    gs (𝟙 Y) y _ ((secEquiv σ hU hg s).f i) = gs (𝟙 Y) y _ (s.f (σ i)) :=
  gs_res (𝟙 Y) y (hU i).le hy _
end GlobalTheory.PowSections
