-- Prove2me | solution 1 for GlobalTheory.T.exists_inversion_coordinate_localization_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:15:40.599786+00:00
-- url     : https://prove2.me/submissions/477fb18e-a7e1-4fb0-873e-f7bc88344c52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomialStatement
import Theorems.Thm_GlobalTheory_localizationAway_inv_coordinate


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
theorem _root_.solution : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∃ Q : Polynomial k, Q ≠ 0 ∧ ∃ (σ : Localization.Away P →ₐ[k] Localization.Away Q) (τ : Localization.Away Q →ₐ[k] Localization.Away (Polynomial.X * P)), (τ.comp σ).toRingHom.comp (algebraMap (Polynomial k) (Localization.Away P)) = algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) ∧ τ.toRingHom.comp (algebraMap (Polynomial k) (Localization.Away Q)) = (Polynomial.aeval (algebraMap (Polynomial k) (Localization.Away (Polynomial.X * P)) P * IsLocalization.Away.invSelf (Polynomial.X * P))).toRingHom := by
  first | exact @GlobalTheory.localizationAway_inv_coordinate | exact GlobalTheory.localizationAway_inv_coordinate | (intros; apply GlobalTheory.localizationAway_inv_coordinate <;> assumption)
end _root_.GlobalTheory.T
