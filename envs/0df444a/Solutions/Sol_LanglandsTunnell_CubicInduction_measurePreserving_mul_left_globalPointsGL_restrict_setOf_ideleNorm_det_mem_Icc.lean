-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ec40ef96-9a5b-58fb-b4a7-54d67977dfe4

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace DeterminantSlab

open MeasureTheory NumberField NumberField.TateGlobal LanglandsTunnell.CubicInduction

private theorem ideleNorm_det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ (Matrix.GeneralLinearGroup.det γ)
  have h2 : Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ) =
      Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
    Matrix.GeneralLinearGroup.map_det (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) γ
  unfold ideleNorm
  rw [h2, h]
  simp

private theorem ideleNorm_det_mul_mem_Icc_iff (γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (α β : ℝ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((γ : AdelicGL 3 (𝓞 ℚ) ℚ) * g)) ∈ Set.Icc α β ↔
      ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β := by
  obtain ⟨γ, ⟨γ₀, hγ₀⟩⟩ := γ
  subst hγ₀
  show ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ₀ * g)) ∈ Set.Icc α β ↔ _
  rw [map_mul, ideleNorm_mul, ideleNorm_det_globalPointsGL, one_mul]

private theorem continuous_ideleNorm_det_gl3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  refine (continuous_ideleNorm ℚ).comp (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact Units.continuous_val.matrix_det.congr fun g => (Matrix.GeneralLinearGroup.val_det_apply g).symm
  · exact Units.continuous_coe_inv.matrix_det.congr fun g => by
      rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]

private theorem measurableSet_slab_gl3 (α β : ℝ) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact continuous_ideleNorm_det_gl3.measurable measurableSet_Icc

end DeterminantSlab

open LanglandsTunnell.CubicInduction in

theorem solution
    (a b : ℝ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    MeasurePreserving
      (fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g)
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b})
      ((NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ).restrict
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ
  have h := (measurePreserving_mul_left
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (NumberField.RingOfIntegers ℚ) ℚ)
    (LanglandsTunnell.CubicInduction.globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ)).restrict_preimage
    (DeterminantSlab.measurableSet_slab_gl3 a b)
  have hS : (fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.globalPointsGL 3 (NumberField.RingOfIntegers ℚ) ℚ γ * g) ⁻¹'
      {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} =
      {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} :=
    Set.ext fun g => DeterminantSlab.ideleNorm_det_mul_mem_Icc_iff ⟨_, γ, rfl⟩ g a b
  rwa [hS] at h

end S_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc (solution)
