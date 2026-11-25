-- Prove2me | solution 1 for GlobalTheory.weightedHomogeneousComponent_one_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:44.975257+00:00
-- url     : https://prove2.me/submissions/2469ac63-c46e-4cd8-abbb-9bf03acb2d17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ A : Type*} [CommRing A] (F : MvPolynomial σ A)
    (m : ℤ) : weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) m F =
      if 0 ≤ m then homogeneousComponent m.toNat F else 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent, weight_one_int]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, coeff_homogeneousComponent]
    by_cases h : (a.degree : ℤ) = m
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hm, if_neg (by omega), coeff_zero]
end GlobalTheory
