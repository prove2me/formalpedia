-- Prove2me | solution 1 for GlobalTheory.tauBimult_of_isPullDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:21.203901+00:00
-- url     : https://prove2.me/submissions/4228402a-b89d-4beb-a30c-0733cd9d0423

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_tauBimult_pull

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (_hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ hD hB => TauPull.tauBimult_pull hG hD hB
end GlobalTheory
