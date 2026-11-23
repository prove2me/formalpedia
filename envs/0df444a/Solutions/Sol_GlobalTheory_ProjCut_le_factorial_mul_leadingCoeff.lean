-- Prove2me | solution 1 for GlobalTheory.ProjCut.le_factorial_mul_leadingCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:04.158865+00:00
-- url     : https://prove2.me/submissions/65fb1cbe-7265-4bb2-b82e-c5a9237e0b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_coeff_nonneg_of_eventually_eval_nat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module
open GlobalTheory
open GlobalTheory.ProjCut
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι k : Type*} [Field k]
namespace GlobalTheory.ProjCut
theorem _root_.solution [Finite ι] {I : Ideal (MvPolynomial ι k)} {e d : ℕ}
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece I) H) (hdeg : H.degree ≤ (e : ℕ))
    (hd : 0 < d) (h : ∀ m, d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ))) :
    H.natDegree = e ∧ (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff := by
  have h1 : 0 ≤ (H - Polynomial.C (d : ℚ) * Polynomial.preHilbertPoly ℚ e d).coeff e := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le hdeg ?_)
      refine Polynomial.degree_le_of_natDegree_le ((Polynomial.natDegree_C_mul_le _ _).trans ?_)
      rw [Polynomial.natDegree_preHilbertPoly]
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        eventually_ge_atTop d] with n hn hdn
      have := h (n - d)
      rw [Nat.sub_add_cancel hdn] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul,
        Polynomial.preHilbertPoly_eq_choose_sub_add _ _ hdn, ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_preHilbertPoly_self,
    sub_nonneg] at h1
  have hf : (0 : ℚ) < e.factorial := by exact_mod_cast e.factorial_pos
  have h2 : 0 < H.coeff e := lt_of_lt_of_le (by positivity) h1
  have h3 : H.natDegree = e :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_le_of_degree_le hdeg) h2.ne'
  refine ⟨h3, ?_⟩
  rw [Polynomial.leadingCoeff, h3]
  rwa [← div_eq_mul_inv, div_le_iff₀' hf] at h1
end GlobalTheory.ProjCut
