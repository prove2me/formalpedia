-- Prove2me | solution 1 for GlobalTheory.ThetaGroupFrame.exp_herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:12.18286+00:00
-- url     : https://prove2.me/submissions/46b260dd-5261-4ece-8eab-aedae443a8ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory.ThetaGroupFrame
private lemma herm_swap_eq_zero_of_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (l a : Fin g → ℂ) :
    a ⬝ᵥ Hm.mulVec (star l) = starRingEnd ℂ (l ⬝ᵥ Hm.mulVec (star a)) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply j i]
  simp
  ring
end GlobalTheory.ThetaGroupFrame
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaGroupFrame
namespace GlobalTheory.ThetaGroupFrame
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (l a : Fin g → ℂ) (n : ℤ) (hn : (n : ℝ) = (l ⬝ᵥ Hm.mulVec (star a)).im) :
    cexp (Real.pi * (l ⬝ᵥ Hm.mulVec (star a))) = cexp (Real.pi * (a ⬝ᵥ Hm.mulVec (star l))) := by
  rw [herm_swap_eq_zero_of_eq_zero hH l a]
  have e : (Real.pi : ℂ) * (l ⬝ᵥ Hm.mulVec (star a)) =
      Real.pi * starRingEnd ℂ (l ⬝ᵥ Hm.mulVec (star a)) + n * (2 * Real.pi * Complex.I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, ← hn] <;> ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]
end GlobalTheory.ThetaGroupFrame
