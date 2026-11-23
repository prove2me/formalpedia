-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.eval_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:49.286448+00:00
-- url     : https://prove2.me/submissions/ff770cde-af47-4190-b4a5-6a52ad1952d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect

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
theorem _root_.solution (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton x),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩
end GlobalTheory.PerfectCompletion
