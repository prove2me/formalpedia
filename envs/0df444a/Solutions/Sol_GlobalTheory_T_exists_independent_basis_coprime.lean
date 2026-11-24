-- Prove2me | solution 1 for GlobalTheory.T.exists_independent_basis_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:05.88361+00:00
-- url     : https://prove2.me/submissions/749f0cad-0192-4dd3-98ab-eb61c16a5a78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprimeStatement
import Theorems.Thm_GlobalTheory_CoprimeBasis_exists_coprime_basis


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M] (N : ℕ), 2 ≤ N → ∃ (r : ℕ) (x : Fin r → M), LinearIndependent (𝓞 F) x ∧ ∃ c : 𝓞 F, c ≠ 0 ∧ IsCoprime c (N : 𝓞 F) ∧ ∀ m : M, c • m ∈ Submodule.span (𝓞 F) (Set.range x) := by
  first | exact @GlobalTheory.CoprimeBasis.exists_coprime_basis | exact GlobalTheory.CoprimeBasis.exists_coprime_basis | (intros; apply GlobalTheory.CoprimeBasis.exists_coprime_basis <;> assumption)
end _root_.GlobalTheory.T
