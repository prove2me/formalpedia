-- Prove2me | solution 1 for GlobalTheory.T.exists_X_pow_smul_mem_span_of_finite_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:43.746896+00:00
-- url     : https://prove2.me/submissions/63e07fae-eb8d-452e-8206-e4ae8e649c52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulMemSpanOfFiniteQuot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulMemSpanOfFiniteQuotStatement
import Theorems.Thm_GlobalTheory_exists_X_pow_smul_mem_span_of_finite_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) M) → ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M) := by
  first | exact @GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | exact GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot | (intros; apply GlobalTheory.exists_X_pow_smul_mem_span_of_finite_quot <;> assumption)
end _root_.GlobalTheory.T
