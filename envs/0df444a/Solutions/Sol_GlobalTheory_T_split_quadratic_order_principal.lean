-- Prove2me | solution 1 for GlobalTheory.T.split_quadratic_order_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:09.4711+00:00
-- url     : https://prove2.me/submissions/b23389d4-75a0-4c66-97e9-0fd80f42e54e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipal
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitQuadraticOrderPrincipalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitQuadratic_isPrincipalIdealRing_of_sq_eq_sq


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
theorem _root_.solution : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | exact GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | (intros; apply GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq <;> assumption)
end _root_.GlobalTheory.T
