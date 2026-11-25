-- Prove2me | solution 1 for GlobalTheory.T.factorialWeightedPairing_detPow_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:03.000249+00:00
-- url     : https://prove2.me/submissions/f47f511d-1441-47da-9bb7-7cf83e5a1c93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportional
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Theorems.Thm_GlobalTheory_DetPowPairing_pairing_pow_proportional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (C : Type) [Field C] [CharZero C] (n₀ M Y : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), M ≤ Y → Q.IsHomogeneous (n₀ * M) →
    (∑ A ∈ (cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (Y - M) * Q)) * (∑ A ∈ (cayDet n₀ C ^ M).support, MvPolynomial.coeff A (cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ M)) = (∑ A ∈ (cayDet n₀ C ^ M).support, MvPolynomial.coeff A (cayDet n₀ C ^ M) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) * (∑ A ∈ (cayDet n₀ C ^ Y).support, MvPolynomial.coeff A (cayDet n₀ C ^ Y) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ Y))) := by
  first | exact @GlobalTheory.DetPowPairing.pairing_pow_proportional | exact GlobalTheory.DetPowPairing.pairing_pow_proportional | (intros; apply GlobalTheory.DetPowPairing.pairing_pow_proportional <;> assumption)
end _root_.GlobalTheory.T
