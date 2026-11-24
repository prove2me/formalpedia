-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:33.608627+00:00
-- url     : https://prove2.me/submissions/eb06e113-4607-4a44-bea7-ca18bf6c8fca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Theorems.Thm_GlobalTheory_InertNorm_exists_dvd_mul_map_sub_X


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
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  first | exact @GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X | (intros; apply GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X <;> assumption)
end _root_.GlobalTheory.T
