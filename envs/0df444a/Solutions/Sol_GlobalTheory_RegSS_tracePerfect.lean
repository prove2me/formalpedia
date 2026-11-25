-- Prove2me | solution 1 for GlobalTheory.RegSS.tracePerfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:24.610265+00:00
-- url     : https://prove2.me/submissions/e8c05d28-a16a-4c18-94c8-77b8f92b8010

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReducedFreeAlgebraTraceFormPerfect
import Theorems.Thm_GlobalTheory_RegSS_eq_zero_of_trace_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.RegSS
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution : TracePerfect := by
  unfold TracePerfect
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.Finite F L := Module.Finite.trans E L
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have inj : Function.Injective (Algebra.traceForm E L) := by
    intro x y hxy

    have h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0 := by
      intro z
      have hz := LinearMap.congr_fun hxy z
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply] at hz
      rw [← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]
    exact sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)
  let b := Module.Free.chooseBasis E L
  let g : L →ₗ[E] L := b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L
  have ginj : Function.Injective g := b.toDualEquiv.symm.injective.comp inj
  refine ⟨inj, fun f => ?_⟩
  obtain ⟨x, hx⟩ := (IsArtinian.bijective_of_injective_endomorphism g ginj).2
    (b.toDualEquiv.symm f)
  exact ⟨x, b.toDualEquiv.symm.injective hx⟩
end GlobalTheory.RegSS
