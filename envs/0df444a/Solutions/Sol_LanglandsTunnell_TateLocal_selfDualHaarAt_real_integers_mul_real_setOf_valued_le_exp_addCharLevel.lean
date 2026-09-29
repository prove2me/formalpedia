-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5359ee26-b8ae-579a-9aaa-71343006aacd

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar
open scoped NNReal

open LanglandsTunnell.TateLocal in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K))
        * (selfDualHaarAt K v).real
            {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v))} = 1 := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  have hV := measureReal_setOf_valued_le_exp K v (Measure.addHaarMeasure (integersPositiveCompacts K v))
    (addCharLevel (psiLocal K v))
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set n : ℤ := addCharLevel (psiLocal K v) with hn
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) with hc
  have hdef : selfDualHaarAt K v = c • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  have hO : (Measure.addHaarMeasure (integersPositiveCompacts K v)).real
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    rw [measureReal_def, ← coe_integersPositiveCompacts K v, Measure.addHaarMeasure_self, ENNReal.toReal_one]
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hcR : (c : ℝ) = N ^ (-(n : ℝ) / 2) := by
    rw [hc, NNReal.coe_rpow, NNReal.coe_natCast]
  rw [hdef, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply, hV, hO, mul_one, mul_one, hcR]

  rw [← Real.rpow_intCast, ← mul_assoc, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  have : -(n : ℝ) / 2 + -(n : ℝ) / 2 + ((n : ℤ) : ℝ) = 0 := by ring
  rw [this, Real.rpow_zero]

end S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel (solution)
