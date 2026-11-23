-- Prove2me | solution 1 for GlobalTheory.EigenNorm.hermForm_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:24.239007+00:00
-- url     : https://prove2.me/submissions/4537648e-cabd-4c57-bffb-d4e6352a080e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenNorm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
namespace GlobalTheory.EigenNorm
namespace _root_.GlobalTheory.EigenNorm
theorem _root_.solution (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm w z = starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [Pi.star_apply, Complex.star_def]
  ring
end _root_.GlobalTheory.EigenNorm
end GlobalTheory.EigenNorm
