-- Prove2me | solution 1 for GlobalTheory.RegSS.eq_zero_of_trace_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:04:22.675716+00:00
-- url     : https://prove2.me/submissions/00852cf6-5dc1-4068-b1ec-7c24d4195741

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReducedFreeAlgebraTraceFormPerfect
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.RegSS
open GlobalTheory GlobalTheory.RegSS
namespace GlobalTheory.RegSS
theorem _root_.solution {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by
  have : IsArtinianRing L := IsArtinianRing.of_finite F L
  have : IsSemisimpleRing L := IsArtinianRing.isSemisimpleRing_of_isReduced L

  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hem : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hem

  have htr : LinearMap.trace F L (Algebra.lmul F L e) = 0 := by
    rw [← Algebra.trace_apply, ← ha, mul_comm]
    exact hx a
  have hidem : IsIdempotentElem (Algebra.lmul F L e) := he.map (Algebra.lmul F L)
  have h0 : Algebra.lmul F L e = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun f => f 1) h0
    simpa using this
  rw [he0] at hI
  exact Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))
end GlobalTheory.RegSS
