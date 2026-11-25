-- Prove2me | solution 1 for GlobalTheory.LowCasShift.nsq_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:52.443171+00:00
-- url     : https://prove2.me/submissions/0f21a79f-79b6-4954-af88-981b225ae10a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe

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
open GlobalTheory GlobalTheory.LowCasShift
namespace GlobalTheory.LowCasShift
theorem _root_.solution {n : ℕ} (u : Fin n → ℝ) (s : Fin n) :
    nsq (u - Pi.single s 1) = nsq u - 2 * u s + 1 := by
  have h : ∀ a, (u - Pi.single s 1 : Fin n → ℝ) a * (u - Pi.single s 1 : Fin n → ℝ) a
      = u a * u a + (if a = s then 1 - 2 * u s else 0) := by
    intro a
    by_cases ha : a = s
    · subst ha; simp; ring
    · simp [ha]
  unfold nsq dot
  simp only [h, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  ring
end GlobalTheory.LowCasShift
