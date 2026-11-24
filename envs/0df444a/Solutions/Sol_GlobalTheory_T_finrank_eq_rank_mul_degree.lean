-- Prove2me | solution 1 for GlobalTheory.T.finrank_eq_rank_mul_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:24.322623+00:00
-- url     : https://prove2.me/submissions/80f06527-e3af-42fd-aaa9-736d12799c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegreeStatement
import Theorems.Thm_GlobalTheory_finrank_int_eq_of_span_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x → ∀ c : 𝓞 F, c ≠ 0 → (∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x)) → Module.finrank ℤ M = r * Module.finrank ℚ F := by
  first | exact @GlobalTheory.finrank_int_eq_of_span_smul | exact GlobalTheory.finrank_int_eq_of_span_smul | (intros; apply GlobalTheory.finrank_int_eq_of_span_smul <;> assumption)
end _root_.GlobalTheory.T
