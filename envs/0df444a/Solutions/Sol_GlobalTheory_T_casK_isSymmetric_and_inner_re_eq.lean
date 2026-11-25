-- Prove2me | solution 1 for GlobalTheory.T.casK_isSymmetric_and_inner_re_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:51.590403+00:00
-- url     : https://prove2.me/submissions/0e4d73c9-56d5-4ed1-8f9e-37439ccf037b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Theorems.Thm_GlobalTheory_casK_isSymmetric_and_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → LinearMap.IsSymmetric (CasK ε E) ∧ ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.casK_isSymmetric_and_form | exact GlobalTheory.casK_isSymmetric_and_form | (intros; apply GlobalTheory.casK_isSymmetric_and_form <;> assumption)
end _root_.GlobalTheory.T
