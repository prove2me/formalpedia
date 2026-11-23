-- Prove2me | solution 1 for GlobalTheory.PeriodChart.isHermitian_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:03.390482+00:00
-- url     : https://prove2.me/submissions/11055d9e-28a6-4a72-b740-bb5cbd751e10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (G : Matrix (Fin g) (Fin g) ℂ) :
    G.IsHermitian ↔ ∀ z w, sesq G z w = starRingEnd ℂ (sesq G w z) := by
  constructor
  · intro hG z w
    rw [sesq_apply, sesq_apply, hermForm, hermForm]
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, Complex.star_def,
      Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : starRingEnd ℂ (G i j) = G j i := by
      have := congrFun (congrFun hG j) i
      simpa [Matrix.conjTranspose_apply, Complex.star_def] using this
    rw [hij]
    ring
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [sesq_single, sesq_single] at this
    simp [Matrix.conjTranspose_apply, this]
end GlobalTheory.PeriodChart
