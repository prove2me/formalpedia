-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_near_one_small_off_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:17:58.186378+00:00
-- url     : https://prove2.me/submissions/fde87463-fbe3-4adb-a26b-d4754e4f66ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegralStatement
import Theorems.Thm_GlobalTheory_crt_approx_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω) (c : ℕ), c ≠ 0 → ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧ ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) → A.valuation (σ t) ≤ A.valuation (c : Ω) := by
  first | exact @GlobalTheory.crt_approx_integral | exact GlobalTheory.crt_approx_integral | (intros; apply GlobalTheory.crt_approx_integral <;> assumption)
end _root_.GlobalTheory.T
