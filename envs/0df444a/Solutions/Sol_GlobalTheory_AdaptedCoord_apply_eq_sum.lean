-- Prove2me | solution 1 for GlobalTheory.AdaptedCoord.apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:59.879794+00:00
-- url     : https://prove2.me/submissions/6d5daed0-4d6c-46f9-96a7-64660f60d8ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.AdaptedCoord
theorem _root_.solution (S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin g → ℂ) (i : Fin g) :
    S v i = ∑ j, S (Pi.single j 1) i * v j := by
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, Finset.sum_apply, mul_comm]
end GlobalTheory.AdaptedCoord
