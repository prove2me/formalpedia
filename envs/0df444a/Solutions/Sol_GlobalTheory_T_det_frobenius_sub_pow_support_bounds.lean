-- Prove2me | solution 1 for GlobalTheory.T.det_frobenius_sub_pow_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:00:57.999075+00:00
-- url     : https://prove2.me/submissions/3c801e17-139d-4f00-abbe-1fe68acbfe64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Theorems.Thm_GlobalTheory_det_frobenius_sub_pow_support


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
theorem _root_.solution : (∀ (l i E n₀ s : ℕ), l.Prime → 1 ≤ i → ∀ ψ : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ,
    ψ = (Matrix.of fun b c : Fin n₀ => (MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) - MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial ((Fin n₀ × Fin n₀) ⊕ (Fin n₀ × Fin n₀)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n₀ ℤ) ^ (l ^ i) →
    ∀ m ∈ (ψ ^ s).support, (∑ q, m (Sum.inr q)) ≤ n₀ * s ∧ (∑ q, m (Sum.inl q)) + l ^ i * ∑ q, m (Sum.inr q) = n₀ * l ^ i * s ∧
      (l : ℤ) ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ MvPolynomial.coeff m (ψ ^ s)) := by
  first | exact @GlobalTheory.det_frobenius_sub_pow_support | exact GlobalTheory.det_frobenius_sub_pow_support | (intros; apply GlobalTheory.det_frobenius_sub_pow_support <;> assumption)
end _root_.GlobalTheory.T
