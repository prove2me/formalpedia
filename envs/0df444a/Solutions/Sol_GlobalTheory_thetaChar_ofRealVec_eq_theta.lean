-- Prove2me | solution 1 for GlobalTheory.thetaChar_ofRealVec_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:42.659079+00:00
-- url     : https://prove2.me/submissions/4842a44c-a902-44a4-ad7f-f3af8bb4d0e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts

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
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) :
    thetaChar τ (ofRealVec a) (ofRealVec b) = fun z => theta a b z τ := by
  funext z
  unfold thetaChar theta thetaTerm eC
  refine tsum_congr fun n => ?_
  have h : ((fun i => (n i : ℂ)) + ofRealVec a) = shiftVec a n := rfl
  rw [h]
  congr 1
  ring
end GlobalTheory
