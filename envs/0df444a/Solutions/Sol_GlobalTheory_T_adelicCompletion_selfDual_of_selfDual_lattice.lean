-- Prove2me | solution 1 for GlobalTheory.T.adelicCompletion_selfDual_of_selfDual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:25.403844+00:00
-- url     : https://prove2.me/submissions/5cda4465-38a4-44a8-960f-adedb725c1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Theorems.Thm_GlobalTheory_AdLat_hat_selfDual


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → ∀ z : Fin n → RA F E, (∀ y ∈ L, hermA c G z (fv F y) ∈ hat1 F (J : Set E)) ↔ z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_selfDual | exact GlobalTheory.AdLat.hat_selfDual | (intros; apply GlobalTheory.AdLat.hat_selfDual <;> assumption)
end _root_.GlobalTheory.T
