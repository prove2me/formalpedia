-- Prove2me | solution 1 for GlobalTheory.Chow.ringKrullDim_eq_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:10:41.435111+00:00
-- url     : https://prove2.me/submissions/a60a6969-ef67-4341-ae9f-9535432971a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution (R S : Type*) [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsIntegral R S] :
    ringKrullDim S = ringKrullDim R := by
  refine le_antisymm (Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun P Q h => Ideal.IsIntegral.comap_lt_comap (R := R) h) (iSup_le fun l => ?_)
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S)
    l.head.asIdeal (by simp [(RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective R S)])
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L
end GlobalTheory.Chow
