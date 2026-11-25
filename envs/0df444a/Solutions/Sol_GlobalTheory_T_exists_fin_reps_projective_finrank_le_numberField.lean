-- Prove2me | solution 1 for GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:17:49.039152+00:00
-- url     : https://prove2.me/submissions/dbf668f7-cf9d-4803-b396-2681487b4cb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFinRepsProjectiveFinrankLeNumberFieldStatement
import Theorems.Thm_GlobalTheory_exists_fin_reps_projective_finrank_le


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  first | exact @GlobalTheory.exists_fin_reps_projective_finrank_le | exact GlobalTheory.exists_fin_reps_projective_finrank_le | (intros; apply GlobalTheory.exists_fin_reps_projective_finrank_le <;> assumption)
end _root_.GlobalTheory.T
