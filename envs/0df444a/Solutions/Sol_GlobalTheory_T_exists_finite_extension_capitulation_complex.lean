-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_extension_capitulation_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:20:31.500421+00:00
-- url     : https://prove2.me/submissions/e8717956-bf05-442d-b2f7-64253fa110fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteExtensionCapitulationComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFiniteExtensionCapitulationComplexStatement
import Theorems.Thm_GlobalTheory_exists_finite_extension_capitulation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  first | exact @GlobalTheory.exists_finite_extension_capitulation | exact GlobalTheory.exists_finite_extension_capitulation | (intros; apply GlobalTheory.exists_finite_extension_capitulation <;> assumption)
end _root_.GlobalTheory.T
