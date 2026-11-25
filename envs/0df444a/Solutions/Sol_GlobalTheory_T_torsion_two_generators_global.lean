-- Prove2me | solution 1 for GlobalTheory.T.torsion_two_generators_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:52.597808+00:00
-- url     : https://prove2.me/submissions/2559530b-66bc-4111-bdef-9de339f17eb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobalStatement
import Theorems.Thm_GlobalTheory_torsion_gens_glue_of_local


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) →
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  first | exact @GlobalTheory.torsion_gens_glue_of_local | exact GlobalTheory.torsion_gens_glue_of_local | (intros; apply GlobalTheory.torsion_gens_glue_of_local <;> assumption)
end _root_.GlobalTheory.T
