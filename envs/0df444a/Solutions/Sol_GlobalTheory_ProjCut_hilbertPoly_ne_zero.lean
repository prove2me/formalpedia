-- Prove2me | solution 1 for GlobalTheory.ProjCut.hilbertPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:03.942779+00:00
-- url     : https://prove2.me/submissions/42efe703-27a9-4020-b7d7-a84276ef5a2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IntegralStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Theorems.Thm_GlobalTheory_quotPiece_natCast


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
theorem _root_.solution {P : Ideal (MvPolynomial ι k)} [P.IsPrime] (hne : ∃ i, X i ∉ P)
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece P) H) : H ≠ 0 := by
  rintro rfl
  obtain ⟨n, hn, hn0⟩ := (hH.eventually_eq.and (eventually_ge_atTop 0)).exists
  lift n to ℕ using hn0
  haveI := hH.finite n
  have hbot : quotPiece P (n : ℤ) = ⊥ := by simpa using hn
  obtain ⟨i, hi⟩ := hne
  have hmem : Ideal.Quotient.mk P (X i ^ n) ∈ quotPiece P (n : ℤ) := by
    rw [quotPiece_natCast]
    exact ⟨X i ^ n, isHomogeneous_X_pow i n, rfl⟩
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hi (Ideal.IsPrime.mem_of_pow_mem ‹_› n hmem)
end GlobalTheory.ProjCut
