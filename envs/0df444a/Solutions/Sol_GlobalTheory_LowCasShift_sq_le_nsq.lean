-- Prove2me | solution 1 for GlobalTheory.LowCasShift.sq_le_nsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:15.012649+00:00
-- url     : https://prove2.me/submissions/9f2400c0-c667-4496-ab4c-4059806fc834

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
theorem _root_.solution {n : ℕ} (u : Fin n → ℝ) (a : Fin n) : u a * u a ≤ nsq u := by
  unfold nsq dot
  exact single_le_sum (f := fun a => u a * u a) (fun i _ => mul_self_nonneg _) (mem_univ a)
end GlobalTheory.LowCasShift
