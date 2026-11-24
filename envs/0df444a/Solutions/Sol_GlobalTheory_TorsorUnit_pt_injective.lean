-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:33:05.507828+00:00
-- url     : https://prove2.me/submissions/11b76860-edab-4770-949f-69a38850b6ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_le_pt_preimage
import Theorems.Thm_GlobalTheory_TorsorUnit_pt_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}
namespace GlobalTheory.TorsorUnit
theorem _root_.solution (hU : IsAffineOpen U) {θ θ' : Γ(Y, U) →+* Γ(Z, ⊤)} (h : pt hU θ = pt hU θ') :
    θ = θ' := by
  have h1 := pt_appLE hU θ (le_pt_preimage hU θ)
  have h2 := pt_appLE hU θ' (le_pt_preimage hU θ')
  rw [← h1, ← h2]
  congr 2
end GlobalTheory.TorsorUnit
