-- Prove2me | solution 1 for GlobalTheory.T.compactCasimirLe_subspace_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:58.939862+00:00
-- url     : https://prove2.me/submissions/872738f5-8cfa-4a6d-a273-a2ec1f81c33c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotone
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotoneStatement
import Theorems.Thm_GlobalTheory_casKLe_subspace_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  first | exact @GlobalTheory.casKLe_subspace_mono | exact GlobalTheory.casKLe_subspace_mono | (intros; apply GlobalTheory.casKLe_subspace_mono <;> assumption)
end _root_.GlobalTheory.T
