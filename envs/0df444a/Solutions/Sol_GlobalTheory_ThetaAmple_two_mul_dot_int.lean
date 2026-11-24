-- Prove2me | solution 1 for GlobalTheory.ThetaAmple.two_mul_dot_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:29:56.719303+00:00
-- url     : https://prove2.me/submissions/d5aa8a58-279c-4da8-921d-1baa1dc74d8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel

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
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution {g : ℕ} {a : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (n : Fin g → ℤ) :
    ∃ k : ℤ, 2 * (ofRealVec a ⬝ᵥ ofIntVec n) = k := by
  have : ∀ i, ∃ k : ℤ, 2 * (a i : ℂ) = k := fun i => by
    rcases ha i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose k hk using this
  refine ⟨∑ i, k i * n i, ?_⟩
  simp only [dotProduct, ofRealVec, ofIntVec, Finset.mul_sum, Int.cast_sum, Int.cast_mul, ← hk, _root_.mul_assoc]
end GlobalTheory.ThetaAmple
