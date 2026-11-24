-- Prove2me | solution 1 for GlobalTheory.ChartRing.isPrecomplete_comap_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:13.7158+00:00
-- url     : https://prove2.me/submissions/f0bc253c-f845-4ff8-9de3-6b17398d7b42

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
theorem _root_.solution [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  prec' F hF := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢
    have : ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n := by
      intro i
      have := IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by
        intro m n h
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using hF (show m + i ≤ n + i by omega) i)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
    choose L hL using this
    refine ⟨mk L, fun n i => ?_⟩
    rcases le_or_gt i n with h | h
    · have := hL i (n - i)
      rw [Nat.sub_add_cancel h] at this
      simpa using this
    · rw [show n - i = 0 by omega]; simp
end GlobalTheory.ChartRing
