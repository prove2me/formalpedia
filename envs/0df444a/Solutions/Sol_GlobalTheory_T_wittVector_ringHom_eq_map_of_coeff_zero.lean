-- Prove2me | solution 1 for GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:58.666307+00:00
-- url     : https://prove2.me/submissions/86135629-b09a-4945-ba64-d22f628c0a62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorRingHomEqMapOfCoeffZeroStatement
import Theorems.Thm_GlobalTheory_WittMapUniq_eq_map_of_coeff_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l] (F : WittVector l R →+* WittVector l O) (ψ : R →+* O), (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  first | exact @GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | exact GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | (intros; apply GlobalTheory.WittMapUniq.eq_map_of_coeff_zero <;> assumption)
end _root_.GlobalTheory.T
