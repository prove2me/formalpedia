-- Prove2me | solution 1 for GlobalTheory.mvEvalAdic_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:51.507547+00:00
-- url     : https://prove2.me/submissions/e73b66e7-ca53-49e5-9afa-d895ebff5ae9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_eq_of_forall_sub_mem_ideal_pow
import Theorems.Thm_GlobalTheory_mvEvalAdic_sub_aeval_truncTotal_mem
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (J : Ideal S) [IsAdicComplete J S] (x : σ → S)
    (hx : ∀ i, x i ∈ J) (p : MvPolynomial σ A) :
    mvEvalAdic A J x hx p = MvPolynomial.aeval x p := by
  refine eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  have h1 := mvEvalAdic_sub_aeval_truncTotal_mem J x hx n (p : MvPowerSeries σ A)
  have h2 : MvPolynomial.aeval x (truncTotal n (p : MvPowerSeries σ A) - p) ∈ J ^ n := by
    refine aeval_mem_pow_of_mem_idealOfVars hx ?_
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hd, MvPolynomial.coeff_coe, sub_self]
  simpa using add_mem h1 h2
end GlobalTheory
