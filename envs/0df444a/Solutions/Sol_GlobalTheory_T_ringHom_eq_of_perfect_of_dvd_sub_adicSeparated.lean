-- Prove2me | solution 1 for GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:41.837857+00:00
-- url     : https://prove2.me/submissions/b104022c-ff69-4243-b5c2-7c36aa2128c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomEqOfPerfectOfDvdSubAdicSeparatedStatement
import Theorems.Thm_GlobalTheory_ringHom_eq_of_perfect_of_dvd_sub


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  first | exact @GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | exact GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | (intros; apply GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub <;> assumption)
end _root_.GlobalTheory.T
