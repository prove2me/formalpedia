-- Prove2me | solution 1 for GlobalTheory.T.exists_residueClass_near_real_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:51.425802+00:00
-- url     : https://prove2.me/submissions/cc83e3ae-0667-4f80-a589-bbf4e93173bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsResidueClassNearRealEmbeddings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsResidueClassNearRealEmbeddingsStatement
import Theorems.Thm_GlobalTheory_residueClass_relativelyDense


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (m : Ideal (𝓞 F)) (a₀ : 𝓞 F), m ≠ ⊥ → ∃ C : ℝ, ∀ y : (F →+* ℝ) → ℝ, ∃ a : 𝓞 F, a - a₀ ∈ m ∧ ∀ τ : F →+* ℝ, |τ (a : F) - y τ| ≤ C := by
  first | exact @GlobalTheory.residueClass_relativelyDense | exact GlobalTheory.residueClass_relativelyDense | (intros; apply GlobalTheory.residueClass_relativelyDense <;> assumption)
end _root_.GlobalTheory.T
