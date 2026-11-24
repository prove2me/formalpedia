-- Prove2me | solution 1 for GlobalTheory.ChartRing.ker_eq_span_X_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:58:56.415797+00:00
-- url     : https://prove2.me/submissions/9763b7be-8119-4e84-ab01-e3c3923faf64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_X_sub_C_dvd_sub_C
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ChartRing.evalAdic_X
attribute [local simp] GlobalTheory.ChartRing.evalAdic_C

set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A : Type*} [CommRing A]
namespace GlobalTheory.ChartRing
theorem _root_.solution (φ : A⟦X⟧ →ₐ[A] A) :
    RingHom.ker φ = Ideal.span {X - C (φ X)} := by
  apply le_antisymm
  · intro f hf
    have h := X_sub_C_dvd_sub_C φ f
    rw [RingHom.mem_ker.1 hf] at h
    simpa [Ideal.mem_span_singleton] using h
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.2 (φ.commutes _).symm
end GlobalTheory.ChartRing
