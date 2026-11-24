-- Prove2me | solution 1 for GlobalTheory.BK.algebraMap_mem_nonZeroDivisors_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:03.456147+00:00
-- url     : https://prove2.me/submissions/25c88ab3-6d7c-4e18-b2fc-3b4acd73c75d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
namespace GlobalTheory.BK
theorem _root_.solution {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩
end GlobalTheory.BK
