-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.dot_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:56.156266+00:00
-- url     : https://prove2.me/submissions/0b8293ac-9a33-4988-b0f1-8aacf9aec077

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsComplementaryThetaOfLinearMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaComplement
namespace GlobalTheory.ThetaComplement
theorem _root_.solution {g : ℕ} (S : Matrix (Fin g) (Fin g) ℂ) (hS : S.IsSymm) (u v : Fin g → ℂ) :
    u ⬝ᵥ S.mulVec v = v ⬝ᵥ S.mulVec u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS.eq, dotProduct_comm]
end GlobalTheory.ThetaComplement
