-- Prove2me | solution 1 for GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:15.195858+00:00
-- url     : https://prove2.me/submissions/95648200-d9fc-4451-9bee-f8861554cc65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroLinearCombinationMemCommonKernel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroLinearCombinationMemCommonKernelStatement
import Theorems.Thm_GlobalTheory_exists_ne_zero_comb_mem_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_comb_mem_ker | exact GlobalTheory.exists_ne_zero_comb_mem_ker | (intros; apply GlobalTheory.exists_ne_zero_comb_mem_ker <;> assumption)
end _root_.GlobalTheory.T
