-- Prove2me | solution 1 for GlobalTheory.gaussVal_lt_one_iff_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:06.25202+00:00
-- url     : https://prove2.me/submissions/2b2520e3-ce52-40a7-999e-6b6f6886d32c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_gaussVal_lt_iff

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
theorem _root_.solution {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) (g : MvPolynomial σ O) :
    gaussVal v (map (algebraMap O K) g) < 1 ↔ map (IsLocalRing.residue O) g = 0 := by
  rw [gaussVal_lt_iff v one_ne_zero, MvPolynomial.ext_iff]
  refine forall_congr' fun m => ?_
  rw [coeff_map, coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hO.isUnit_iff_valuation_eq_one]
  exact (hO.map_le_one _).lt_iff_ne
end GlobalTheory
