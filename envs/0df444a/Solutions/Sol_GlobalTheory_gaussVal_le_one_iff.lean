-- Prove2me | solution 1 for GlobalTheory.gaussVal_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:03.396863+00:00
-- url     : https://prove2.me/submissions/3719ae5d-67c2-4bc1-9a10-5216fd0ca5c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
namespace GlobalTheory
theorem _root_.solution {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    {f : MvPolynomial σ K} :
    gaussVal v f ≤ 1 ↔ ∃ g : MvPolynomial σ O, map (algebraMap O K) g = f := by
  refine ⟨fun h => ?_, ?_⟩
  · refine (mem_range_map_iff_coeffs_subset.mpr ?_ :
      f ∈ Set.range (map (algebraMap O K)))
    intro c hc
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact hO.exists_of_le_one ((le_gaussVal v f m).trans h)
  · rintro ⟨g, rfl⟩
    exact (gaussVal_le_iff v).mpr fun m => by rw [coeff_map]; exact hO.map_le_one _
end GlobalTheory
