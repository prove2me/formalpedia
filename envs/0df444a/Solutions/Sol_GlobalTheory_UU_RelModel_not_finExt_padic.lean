-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.not_finExt_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:22.022209+00:00
-- url     : https://prove2.me/submissions/9210d40d-a7db-419f-bd75-b1a0d989a446

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight

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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (p : ℕ) [Fact p.Prime] : ¬ FinExt ℤ_[p] ℚ_[p] := fun h => by
  have := h.2.2.2.1.map_nonunit (p : ℤ_[p]) (IsUnit.mk0 _ (by simpa using (Fact.out : p.Prime).ne_zero))
  exact PadicInt.irreducible_p.not_isUnit this
end GlobalTheory.UU.RelModel
