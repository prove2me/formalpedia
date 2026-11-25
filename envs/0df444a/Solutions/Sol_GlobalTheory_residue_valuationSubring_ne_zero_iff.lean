-- Prove2me | solution 1 for GlobalTheory.residue_valuationSubring_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:47.142939+00:00
-- url     : https://prove2.me/submissions/5a9fdf3b-3ca5-41b9-844e-b42e501fdc71

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraicIndependentResidueIffGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {U Γ : Type*} [Field U]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ) (x : v.valuationSubring) :
    IsLocalRing.residue v.valuationSubring x ≠ 0 ↔ v (x : U) = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, ValuationSubring.valuation_eq_one_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).symm.eq_one_iff_eq_one
end GlobalTheory
