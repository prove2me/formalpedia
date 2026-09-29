-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_ne_zero_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/46e821ee-28e7-5528-96ab-c935642ee12c

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open LanglandsTunnell.TateLocal NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s ≠ 0 := by
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hq1' : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hq1 : 1 < Ideal.absNorm v.asIdeal := by omega
  have hq : 0 < Ideal.absNorm v.asIdeal := by omega
  have hqR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  rw [LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified K v χ s hχ hs,
    LanglandsTunnell.TateLocal.selfDualHaarAt_real_units_eq K v,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ]
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [Complex.ofReal_ne_zero]
    refine mul_ne_zero (sub_ne_zero.mpr ?_) (Real.rpow_pos_of_pos hqR0 _).ne'
    exact (inv_lt_one_of_one_lt₀ hqR).ne'
  · refine sub_ne_zero.mpr fun h => ?_
    have hn : ‖(χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
      exact hs
    rw [← h, norm_one] at hn
    exact lt_irrefl _ hn

#print axioms solution

end S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified (solution)
