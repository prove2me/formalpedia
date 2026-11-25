-- Prove2me | solution 1 for GlobalTheory.T.determinantPairing_quotient_valuation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:01.328805+00:00
-- url     : https://prove2.me/submissions/1b806649-97d0-423a-a4e5-5de5e0899649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Theorems.Thm_GlobalTheory_DetPairingBound_main
import Theorems.Thm_GlobalTheory_DetPowPairing_main


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
theorem _root_.solution : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s))))) := by
  first | exact @GlobalTheory.DetPairingBound.main | exact GlobalTheory.DetPairingBound.main | (intros; apply GlobalTheory.DetPairingBound.main <;> assumption)
end _root_.GlobalTheory.T
