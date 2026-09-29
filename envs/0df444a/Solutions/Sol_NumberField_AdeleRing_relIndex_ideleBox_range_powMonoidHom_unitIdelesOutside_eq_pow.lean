-- Prove2me | solution 1 for NumberField.AdeleRing.relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/eefeb448-7abd-52ba-ac24-527aabd146c8

import Mathlib
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_AdeleRing_relIndex_ideleBox_unitIdelesOutside
import Theorems.Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p K).Nonempty)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    (NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers K) K (↑S)
        (fun v => (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        (fun w => (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)).relIndex
      (NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers K) K (↑S))
      = p ^ (2 * (S.card + Fintype.card (NumberField.InfinitePlace K))) := by
  rw [NumberField.AdeleRing.relIndex_ideleBox_unitIdelesOutside]
  simp only [Subgroup.index_eq_card]
  exact NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
    hp hζ S hS

end S_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
end P2MW
export P2MW.S_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow (solution)
