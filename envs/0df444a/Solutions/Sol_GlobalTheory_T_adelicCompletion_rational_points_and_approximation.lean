-- Prove2me | solution 1 for GlobalTheory.T.adelicCompletion_rational_points_and_approximation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:12.161839+00:00
-- url     : https://prove2.me/submissions/ccecb274-f047-42e0-9748-6d7c0fc338da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Theorems.Thm_GlobalTheory_AdLat_hat_rational_points_and_approx


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_rational_points_and_approx | exact GlobalTheory.AdLat.hat_rational_points_and_approx | (intros; apply GlobalTheory.AdLat.hat_rational_points_and_approx <;> assumption)
end _root_.GlobalTheory.T
