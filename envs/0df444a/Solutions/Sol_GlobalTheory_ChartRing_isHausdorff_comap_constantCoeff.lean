-- Prove2me | solution 1 for GlobalTheory.ChartRing.isHausdorff_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:13.012119+00:00
-- url     : https://prove2.me/submissions/e8fdd687-a294-4a32-b6d4-1b445b96fed4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_X
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_C
import Theorems.Thm_GlobalTheory_ChartRing_mem_pow_comap_constantCoeff_iff
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
theorem _root_.solution [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  haus' f hf := by
    ext i
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hf (n + i)
    rw [SModEq.zero] at this ⊢
    simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
    simpa using (mem_pow_comap_constantCoeff_iff I _ f).1 this i
end GlobalTheory.ChartRing
