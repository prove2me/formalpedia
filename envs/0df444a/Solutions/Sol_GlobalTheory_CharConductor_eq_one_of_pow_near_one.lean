-- Prove2me | solution 1 for GlobalTheory.CharConductor.eq_one_of_pow_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:31:16.316335+00:00
-- url     : https://prove2.me/submissions/e89184c8-c554-4c70-99d7-a75a4e561478

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfNormSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Theorems.Thm_GlobalTheory_IterationConvergence_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CharConductor
namespace GlobalTheory.CharConductor
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterationConvergence.main
  | exact _root_.GlobalTheory.IterationConvergence.main
  | (apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterationConvergence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterationConvergence.main ..)
end GlobalTheory.CharConductor
