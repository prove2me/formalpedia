-- Prove2me | solution 1 for GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:37.499521+00:00
-- url     : https://prove2.me/submissions/6677d0c6-7a95-4800-8e29-ae839740413a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationsQuotientBialgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationOfCounitalComul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInvariantDerivationsQuotientBialgebraStatement
import Theorems.Thm_GlobalTheory_quotient_base_change_invariant_derivations


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  first | exact @GlobalTheory.quotient_base_change_invariant_derivations | exact GlobalTheory.quotient_base_change_invariant_derivations | (intros; apply GlobalTheory.quotient_base_change_invariant_derivations <;> assumption)
end _root_.GlobalTheory.T
