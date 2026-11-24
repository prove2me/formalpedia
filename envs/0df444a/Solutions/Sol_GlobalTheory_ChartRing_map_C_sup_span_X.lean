-- Prove2me | solution 1 for GlobalTheory.ChartRing.map_C_sup_span_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:11.014217+00:00
-- url     : https://prove2.me/submissions/49d9872a-d451-4c65-b55f-776788a31e07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
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
variable {A : Type*} [CommRing A] (I : Ideal A)
namespace GlobalTheory.ChartRing
theorem _root_.solution :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · simp [Ideal.span_singleton_le_iff_mem]
  · intro f hf
    rw [f.eq_X_mul_shift_add_const]
    exact add_mem
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
end GlobalTheory.ChartRing
