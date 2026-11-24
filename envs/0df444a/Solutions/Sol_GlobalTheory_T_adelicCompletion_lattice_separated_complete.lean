-- Prove2me | solution 1 for GlobalTheory.T.adelicCompletion_lattice_separated_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:43:04.566442+00:00
-- url     : https://prove2.me/submissions/1564e4e9-4e5b-4904-aea6-251d8c5ac063

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Theorems.Thm_GlobalTheory_AdLat_Complete_hat_separated_complete


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → (∀ z : Fin n → RA F E, (∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = N • w) → z = 0) ∧ ∀ x : ℕ → (Fin n → RA F E), (∀ N, x N ∈ (hat F (L : Set (Fin n → E)))) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ (hat F (L : Set (Fin n → E))), x (N * m) = x N + N • w) → ∃ z ∈ (hat F (L : Set (Fin n → E))), ∀ N : ℕ, 0 < N → ∃ w ∈ (hat F (L : Set (Fin n → E))), z = x N + N • w := by
  first | exact @GlobalTheory.AdLat.Complete.hat_separated_complete | exact GlobalTheory.AdLat.Complete.hat_separated_complete | (intros; apply GlobalTheory.AdLat.Complete.hat_separated_complete <;> assumption)
end _root_.GlobalTheory.T
