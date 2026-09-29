-- Prove2me | solution 1 for NumberField.toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8f0026c9-4455-5d62-ac39-97cb647561a0

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal

namespace BandPos19

open AutomorphicForm NumberField.TateGlobal

theorem centralScalar_mem_setOf_iff (K : Type) [Field K] [NumberField K] {α β : ℝ} (hα : 0 < α)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β ↔
      ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β) := by
  have hu := ideleNorm_pos z
  rw [det_centralScalar, pow_two, ideleNorm_mul, Set.mem_Icc, Set.mem_Icc]
  have hN : Real.sqrt (ideleNorm K z * ideleNorm K z) = ideleNorm K z := Real.sqrt_mul_self hu.le
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := Real.sqrt_le_sqrt h1; rwa [hN] at this
    · have := Real.sqrt_le_sqrt h2; rwa [hN] at this
  · rintro ⟨h1, h2⟩
    have hβ : 0 ≤ β := by
      have : 0 < Real.sqrt β := hu.trans_le h2
      exact (Real.sqrt_pos.1 this).le
    refine ⟨?_, ?_⟩
    · have := mul_self_le_mul_self (Real.sqrt_nonneg α) h1
      rwa [Real.mul_self_sqrt hα.le] at this
    · have := mul_self_le_mul_self hu.le h2
      rwa [Real.mul_self_sqrt hβ] at this

end BandPos19

open AutomorphicForm NumberField.TateGlobal BandPos19 in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK) :
    0 < (νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal := by
  obtain ⟨C, hC, hslab⟩ :=
    NumberField.TateGlobal.exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log K νZK
  have h2 : {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K
        (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 K) K z)) ∈ Set.Icc α β} =
      {z | ideleNorm K z ∈ Set.Icc (Real.sqrt α) (Real.sqrt β)} := by
    ext z; exact centralScalar_mem_setOf_iff K hα z
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.2 hα
  have hsαβ : Real.sqrt α < Real.sqrt β := Real.sqrt_lt_sqrt hα.le hαβ
  have hlog : 0 < Real.log (Real.sqrt β / Real.sqrt α) := Real.log_pos ((one_lt_div hsα).2 hsαβ)
  rw [h2, hslab ΩK hΩK _ _ hsα hsαβ.le, ENNReal.toReal_ofReal (mul_pos hC hlog).le]
  exact mul_pos hC hlog

end S_NumberField_toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain
end P2MW
export P2MW.S_NumberField_toReal_measure_inter_ideleNorm_det_centralScalar_mem_Icc_pos_of_isFundamentalDomain (solution)
