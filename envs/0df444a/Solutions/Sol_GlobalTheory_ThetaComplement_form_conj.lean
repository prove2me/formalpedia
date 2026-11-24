-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.form_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:57.922078+00:00
-- url     : https://prove2.me/submissions/eedb2926-311d-4e8b-94db-ac4de86eae6e

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
theorem _root_.solution {g : ℕ} (H M : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    u ⬝ᵥ (Mᵀ * H * Mᵀᴴ).mulVec (star v) = (M *ᵥ u) ⬝ᵥ H.mulVec (star (M *ᵥ v)) := by
  have h : star (M *ᵥ v) = Mᵀᴴ *ᵥ star v := by
    funext i
    simp [mulVec, dotProduct]
  rw [h, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
end GlobalTheory.ThetaComplement
