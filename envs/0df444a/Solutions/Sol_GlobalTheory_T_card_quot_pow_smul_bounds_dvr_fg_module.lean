-- Prove2me | solution 1 for GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:02.971386+00:00
-- url     : https://prove2.me/submissions/e0e25db4-01ce-436a-90c8-b976b50d50cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModule
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotPowSmulBoundsDvrFgModuleStatement
import Theorems.Thm_GlobalTheory_DVRQuotCount_card_quot_pow_smul_bounds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t → (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤ C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  first | exact @GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | exact GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | (intros; apply GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds <;> assumption)
end _root_.GlobalTheory.T
