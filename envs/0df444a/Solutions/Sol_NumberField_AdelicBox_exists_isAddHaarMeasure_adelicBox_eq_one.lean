-- Prove2me | solution 1 for NumberField.AdelicBox.exists_isAddHaarMeasure_adelicBox_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/69822a24-6285-54cc-b203-5607935199c3

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace P2mSolAdelicBoxHaarOne

theorem main (K : Type) [Field K] [NumberField K]
    [inst : MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 := by

  have hinst : inst = NumberField.AdelicHaar.adeleBorel (𝓞 K) K := BorelSpace.measurable_eq
  subst hinst
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  set μ₀ : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hμ₀
  have h0 : μ₀ (NumberField.AdelicBox.adelicBox K) ≠ 0 :=
    (NumberField.AdelicBox.measure_adelicBox_pos K μ₀).ne'
  have htop : μ₀ (NumberField.AdelicBox.adelicBox K) ≠ ⊤ :=
    (NumberField.AdelicBox.measure_adelicBox_lt_top K μ₀).ne
  refine ⟨(μ₀ (NumberField.AdelicBox.adelicBox K))⁻¹ • μ₀, ?_, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h0)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end P2mSolAdelicBoxHaarOne

theorem solution (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)] :
    ∃ μK : Measure (AdeleRing (𝓞 K) K), μK.IsAddHaarMeasure ∧ μK (NumberField.AdelicBox.adelicBox K) = 1 :=
  P2mSolAdelicBoxHaarOne.main K

end S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one
end P2MW
export P2MW.S_NumberField_AdelicBox_exists_isAddHaarMeasure_adelicBox_eq_one (solution)
