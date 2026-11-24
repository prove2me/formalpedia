-- Prove2me | solution 1 for GlobalTheory.exists_ofRealVec_of_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:35.293128+00:00
-- url     : https://prove2.me/submissions/881fb8a5-3d4b-4e64-bcdb-128ac115edfd

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
theorem _root_.solution {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ a' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) ∧ a = ofRealVec a' := by
  refine ⟨fun i => (a i).re, fun i => ?_, funext fun i => ?_⟩
  · rcases ha i with h | h
    · left; simp [h]
    · right; simp [h]
  · rcases ha i with h | h <;> simp [ofRealVec, h]
end GlobalTheory
