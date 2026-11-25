-- Prove2me | solution 1 for GlobalTheory.T.exists_rational_unitary_split_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:10.720112+00:00
-- url     : https://prove2.me/submissions/8ddf7083-6f18-4a9f-86d5-5d4834557657

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Theorems.Thm_GlobalTheory_UnRep_LatForm_exists_rep_split_denominator


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
end _root_.GlobalTheory.T
