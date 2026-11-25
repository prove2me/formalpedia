-- Prove2me | solution 1 for GlobalTheory.T.unramified_quadratic_order_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:49.10754+00:00
-- url     : https://prove2.me/submissions/e62a3fae-df63-44a0-a661-a9301d4d5669

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipal
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuadraticOrderPrincipalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadraticUnit_isPrincipalIdealRing_of_nonsquare_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R] [CommRing O] (ι : R →+* O) (δ : O) (D : R), δ * δ = ι D → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit D → IsUnit (2 : R) → (¬ ∃ e : R, D = e * e) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | exact GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit | (intros; apply GlobalTheory.CompanionTheory.QuadraticUnit.isPrincipalIdealRing_of_nonsquare_unit <;> assumption)
end _root_.GlobalTheory.T
