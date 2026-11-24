-- Prove2me | solution 1 for GlobalTheory.T.exists_rational_matrix_approx_adele_linear_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:25.739832+00:00
-- url     : https://prove2.me/submissions/143e3c5f-57c2-4801-8d6d-897a264192c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Theorems.Thm_GlobalTheory_UnRep_exists_rational_approx_after_adele_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (φ : Matrix (Fin n) (Fin n) (RA F E) →+ Matrix (Fin n) (Fin n) (RA F E)), (∀ (a : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), φ ((a ⊗ₜ[F] (1 : E) : RA F E) • M) = (a ⊗ₜ[F] (1 : E) : RA F E) • φ M) → ∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), φ (M - fm F M₀) *ᵥ z = D • w := by
  first | exact @GlobalTheory.UnRep.exists_rational_approx_after_adele_linear | exact GlobalTheory.UnRep.exists_rational_approx_after_adele_linear | (intros; apply GlobalTheory.UnRep.exists_rational_approx_after_adele_linear <;> assumption)
end _root_.GlobalTheory.T
