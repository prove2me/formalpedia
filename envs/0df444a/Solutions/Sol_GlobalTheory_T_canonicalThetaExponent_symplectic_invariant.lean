-- Prove2me | solution 1 for GlobalTheory.T.canonicalThetaExponent_symplectic_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:26.739278+00:00
-- url     : https://prove2.me/submissions/395dc3fa-bec4-4aed-8364-fb801a53e407

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CanonicalThetaExponentSymplecticInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CanonicalThetaExponentSymplecticInvariantStatement
import Theorems.Thm_GlobalTheory_SW_canon_exponent_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  first | exact @GlobalTheory.SW.canon_exponent_invariant | exact GlobalTheory.SW.canon_exponent_invariant | (intros; apply GlobalTheory.SW.canon_exponent_invariant <;> assumption)
end _root_.GlobalTheory.T
