-- Prove2me | solution 1 for NumberField.TateGlobal.exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a3b249c2-bf5c-5109-83d8-ef4b4d01a1fd

import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain NumberField.TateGlobal Set

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 < C ∧
      ∀ Ω : Set (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          ν (Ω ∩ {t | NumberField.TateGlobal.ideleNorm F t ∈ Set.Icc a b}) = ENNReal.ofReal (C * Real.log (b / a)) := by
  obtain ⟨C, hC, hK⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div F ν
  refine ⟨C, hC, fun Ω hΩ a b ha hab => ?_⟩
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨h1, -, -⟩ := hK Ω hΩ

  set g : ℝ → ℂ := (Icc a b).indicator fun _ => (1 : ℂ) with hg_def
  have hgm : Measurable g := measurable_const.indicator measurableSet_Icc
  obtain ⟨hiff, heq⟩ := h1 g hgm

  set T : Set (AdeleRing (𝓞 F) F)ˣ := {t | ideleNorm F t ∈ Icc a b} with hT_def
  have hTm : MeasurableSet T :=
    (NumberField.TateGlobal.continuous_ideleNorm F).measurable measurableSet_Icc
  have hcomp : (fun x : (AdeleRing (𝓞 F) F)ˣ => g (ideleNorm F x)) = T.indicator fun _ => (1 : ℂ) := by
    funext x
    simp only [hg_def, hT_def, Set.indicator_apply, Set.mem_setOf_eq]

  have hprod : (fun r : ℝ => (r : ℂ)⁻¹ * g r) = (Icc a b).indicator fun r : ℝ => ((r : ℂ)⁻¹) := by
    funext r
    by_cases hr : r ∈ Icc a b
    · simp only [hg_def, Set.indicator_of_mem hr, mul_one]
    · simp only [hg_def, Set.indicator_of_notMem hr, mul_zero]
  have hinter : Ioi (0 : ℝ) ∩ Icc a b = Icc a b := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, mem_Icc]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨ha.trans_le h.1, h⟩
  have hcont : ContinuousOn (fun r : ℝ => ((r : ℂ)⁻¹)) (Icc a b) := by
    refine (Complex.continuous_ofReal.continuousOn.inv₀ fun r hr => ?_)
    exact_mod_cast (ha.trans_le hr.1).ne'
  have hintI : IntegrableOn (fun r : ℝ => (r : ℂ)⁻¹ * g r) (Ioi (0 : ℝ)) := by
    rw [hprod, IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Icc, Set.inter_comm, hinter]
    exact hcont.integrableOn_compact isCompact_Icc
  have hRHS : ∫ r in Ioi (0 : ℝ), (r : ℂ)⁻¹ * g r = ((Real.log (b / a) : ℝ) : ℂ) := by
    rw [hprod, setIntegral_indicator measurableSet_Icc, hinter, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
    have h2 : (fun r : ℝ => ((r : ℂ)⁻¹)) = fun r : ℝ => ((r⁻¹ : ℝ) : ℂ) := by
      funext r; rw [Complex.ofReal_inv]
    rw [h2, intervalIntegral.integral_ofReal, integral_inv_of_pos ha hb]

  have hintL : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ => g (ideleNorm F x)) Ω ν := hiff.mpr hintI
  have hfin : ν (Ω ∩ T) < ⊤ := by
    rw [hcomp, IntegrableOn, integrable_indicator_iff hTm, IntegrableOn, Measure.restrict_restrict hTm, Set.inter_comm] at hintL
    have := (integrableOn_const_iff (C := (1 : ℂ)) (s := Ω ∩ T) (μ := ν)).mp hintL
    exact this.resolve_left (by simp)
  have hLHS : ∫ x in Ω, g (ideleNorm F x) ∂ν = ((ν (Ω ∩ T)).toReal : ℂ) := by
    rw [hcomp, setIntegral_indicator hTm, setIntegral_const, Complex.real_smul, mul_one, measureReal_def]

  have hval : (ν (Ω ∩ T)).toReal = C * Real.log (b / a) := by
    have h := heq
    rw [hLHS, hRHS] at h
    exact_mod_cast h
  rw [← ENNReal.ofReal_toReal hfin.ne, hval]

#print axioms solution

end S_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_pos_forall_measure_inter_setOf_ideleNorm_mem_Icc_eq_ofReal_mul_log (solution)
