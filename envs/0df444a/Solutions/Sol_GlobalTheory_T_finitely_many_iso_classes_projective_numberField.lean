-- Prove2me | solution 1 for GlobalTheory.T.finitely_many_iso_classes_projective_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:32.50303+00:00
-- url     : https://prove2.me/submissions/5809a2f2-30db-4d78-bb39-34f675d62b1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberFieldStatement
import Theorems.Thm_GlobalTheory_ProjModFinIso_finitely_many_iso_classes


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  first | exact @GlobalTheory.ProjModFinIso.finitely_many_iso_classes | exact GlobalTheory.ProjModFinIso.finitely_many_iso_classes | (intros; apply GlobalTheory.ProjModFinIso.finitely_many_iso_classes <;> assumption)
end _root_.GlobalTheory.T
