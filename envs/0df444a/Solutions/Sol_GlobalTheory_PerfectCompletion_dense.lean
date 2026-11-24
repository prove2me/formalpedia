-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:20.233774+00:00
-- url     : https://prove2.me/submissions/02d6b5c5-9255-4801-8bd0-998888838280

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
import Theorems.Thm_GlobalTheory_PerfectCompletion_eval_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {x}) V r y)
  have : AdicCompletion.eval (Ideal.span {x}) V r (y - algebraMap V _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff x r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩
end GlobalTheory.PerfectCompletion
