-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnBasis.eta_mul_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:08.513074+00:00
-- url     : https://prove2.me/submissions/51293a9f-8780-415e-8e5f-ccca95dc8d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnBasis
namespace GlobalTheory.UnitLemma.SgnBasis
theorem _root_.solution (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]
end GlobalTheory.UnitLemma.SgnBasis
