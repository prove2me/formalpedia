-- Prove2me | solution 1 for GlobalTheory.ChartRing.evalAdic_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:42.432575+00:00
-- url     : https://prove2.me/submissions/4360f340-43e9-4935-81e4-394e6eef32f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
import Theorems.Thm_GlobalTheory_ChartRing_evalAdic_sub_aeval_trunc_mem
import Theorems.Thm_GlobalTheory_ChartRing_eq_of_forall_sub_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)
namespace GlobalTheory.ChartRing
theorem _root_.solution : evalAdic A J hs X = s := by
  refine eq_of_forall_sub_mem_pow J fun n => ?_
  have h1 := evalAdic_sub_aeval_trunc_mem J hs n (X : A⟦X⟧)
  have h2 : Polynomial.aeval s (trunc n (X : A⟦X⟧)) -
      Polynomial.aeval s (Polynomial.X : Polynomial A) ∈ J ^ n :=
    aeval_sub_mem_pow hs fun i hi => by
      simp [coeff_trunc, hi, coeff_X, Polynomial.coeff_X, eq_comm]
  simpa using add_mem h1 h2
end GlobalTheory.ChartRing
