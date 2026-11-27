-- Prove2me | solution 1 for GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:05:21.148152+00:00
-- url     : https://prove2.me/submissions/10aa7181-bdd5-4ab3-8891-73c44799f8bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwinerMemISupRangeEqSumSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwinerMemISupRangeEqSumSmulStatement
import Theorems.Thm_GlobalTheory_intertwiner_mem_iSup_range_eq_sum_smul


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
theorem _root_.solution : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X),
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) →
    ∀ ψ : π.IntertwiningMap ρ, LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap →
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  first | exact @GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | exact GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | (intros; apply GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul <;> assumption)
end _root_.GlobalTheory.T
