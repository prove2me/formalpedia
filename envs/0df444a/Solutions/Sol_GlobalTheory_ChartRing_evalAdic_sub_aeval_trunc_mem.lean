-- Prove2me | solution 1 for GlobalTheory.ChartRing.evalAdic_sub_aeval_trunc_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:50.30909+00:00
-- url     : https://prove2.me/submissions/acd0ef00-47bc-45fb-9975-ea52015a3563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

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
theorem _root_.solution (n : ℕ) (f : A⟦X⟧) :
    evalAdic A J hs f - Polynomial.aeval s (trunc n f) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq]
  exact IsAdicComplete.mk_liftAlgHom J (evalMod A J hs) (factor_comp_evalMod J hs) n f
end GlobalTheory.ChartRing
