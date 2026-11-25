-- Prove2me | solution 1 for GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:30.533284+00:00
-- url     : https://prove2.me/submissions/73cf0ea6-8459-4b5a-819d-fe6ce9da7e79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdealStatement
import Theorems.Thm_GlobalTheory_wittVector_dvd_of_saturated_ideal


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J → (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) → ∀ a ∈ J, μ ∣ a := by
  first | exact @GlobalTheory.wittVector_dvd_of_saturated_ideal | exact GlobalTheory.wittVector_dvd_of_saturated_ideal | (intros; apply GlobalTheory.wittVector_dvd_of_saturated_ideal <;> assumption)
end _root_.GlobalTheory.T
