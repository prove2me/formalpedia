-- Prove2me | solution 1 for GlobalTheory.ThetaComplement.im_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:58.958803+00:00
-- url     : https://prove2.me/submissions/8c90d8be-9a04-4234-9b05-be766e7e2b6c

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
theorem _root_.solution {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hH : H.IsHermitian) (u v : Fin g → ℂ) :
    2 * I * ((u ⬝ᵥ H.mulVec (star v)).im : ℂ)
      = u ⬝ᵥ H.mulVec (star v) - v ⬝ᵥ H.mulVec (star u) := by
  have h : v ⬝ᵥ H.mulVec (star u) = star (u ⬝ᵥ H.mulVec (star v)) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  rw [h, star_def, Complex.sub_conj]
  push_cast; ring
end GlobalTheory.ThetaComplement
