-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6101287d-6851-504d-aee8-200bf0eb7364

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal

namespace EquivQ

theorem isAddHaarMeasure_selfDualHaarAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end EquivQ

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) (w : Fin 2 → p.adicCompletion ℚ) :
    letI := localBorel ℚ p
    ∫ u : Fin 2 → p.adicCompletion ℚ, Φ (fun j : Fin 2 => u 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + u 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
        NumberField.StandardAddChar.psiLocal ℚ p (u 1 * w 0 - u 0 * w 1) ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) =
      (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ))⁻¹ *
        ∫ u : Fin 2 → p.adicCompletion ℚ, Φ u *
          NumberField.StandardAddChar.psiLocal ℚ p
            (u 1 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0)) -
             u 0 * (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)⁻¹ * (w 0 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 + w 1 * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)))
          ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  classical
  letI instMS : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := EquivQ.isAddHaarMeasure_selfDualHaarAt p
  haveI : (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : BorelSpace (Fin 2 → p.adicCompletion ℚ) := Pi.borelSpace
  set G : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) with hG
  set d : p.adicCompletion ℚ := ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) with hd
  have hdG : G.det = d := by rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
  have hd0 : d ≠ 0 := by rw [hd]; exact Units.ne_zero _

  set T : (Fin 2 → p.adicCompletion ℚ) →ₗ[p.adicCompletion ℚ] (Fin 2 → p.adicCompletion ℚ) := Matrix.toLin' G.transpose with hT
  have hTapply : ∀ u : Fin 2 → p.adicCompletion ℚ, T u = fun j : Fin 2 => u 0 * G 0 j + u 1 * G 1 j := by
    intro u; funext j
    rw [hT, Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
    ring
  have hdetT : LinearMap.det T = d := by rw [hT, LinearMap.det_toLin', Matrix.det_transpose, hdG]
  have hTc : Continuous T := by
    have : (T : (Fin 2 → p.adicCompletion ℚ) → (Fin 2 → p.adicCompletion ℚ)) = fun u => fun j : Fin 2 => u 0 * G 0 j + u 1 * G 1 j :=
      funext hTapply
    rw [this]
    exact continuous_pi fun j => by fun_prop

  have hmap := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure ℚ p
    (Fin 2 → p.adicCompletion ℚ) (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) T (by rw [hdetT]; exact hd0)

  set c0 : p.adicCompletion ℚ := d⁻¹ * (w 0 * G 0 0 + w 1 * G 1 0) with hc0
  set c1 : p.adicCompletion ℚ := d⁻¹ * (w 0 * G 0 1 + w 1 * G 1 1) with hc1
  set H : (Fin 2 → p.adicCompletion ℚ) → ℂ := fun u' =>
    Φ u' * NumberField.StandardAddChar.psiLocal ℚ p (u' 1 * c0 - u' 0 * c1) with hH
  have hphase : ∀ u : Fin 2 → p.adicCompletion ℚ,
      (T u) 1 * c0 - (T u) 0 * c1 = u 1 * w 0 - u 0 * w 1 := by
    intro u
    rw [hTapply]
    simp only [hc0, hc1]
    have hdet2 : d = G 0 0 * G 1 1 - G 0 1 * G 1 0 := by rw [← hdG, Matrix.det_fin_two]
    field_simp
    rw [hdet2]; ring
  have hcomp : ∀ u : Fin 2 → p.adicCompletion ℚ,
      Φ (fun j : Fin 2 => u 0 * G 0 j + u 1 * G 1 j) * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * w 0 - u 0 * w 1) = H (T u) := by
    intro u
    have : H (T u) = Φ (T u) * NumberField.StandardAddChar.psiLocal ℚ p ((T u) 1 * c0 - (T u) 0 * c1) := rfl
    rw [this, hphase u, hTapply]
  have hHm : AEStronglyMeasurable H (Measure.map T (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) := by
    refine (Continuous.mul hΦ.1.continuous ?_).aestronglyMeasurable
    exact (NumberField.StandardAddChar.continuous_psiLocal (K := ℚ) (v := p)).comp (by fun_prop)
  calc (∫ u, Φ (fun j : Fin 2 => u 0 * G 0 j + u 1 * G 1 j) * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * w 0 - u 0 * w 1)
          ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p))
      = ∫ u, H (T u) ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by simp_rw [hcomp]
    _ = ∫ u', H u' ∂(Measure.map T (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) :=
          (integral_map hTc.measurable.aemeasurable hHm).symm
    _ = (‖LinearMap.det T‖⁻¹ : ℝ) • ∫ u', H u' ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
          rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 (norm_nonneg _))]
    _ = _ := by
          rw [hdetT, Complex.real_smul, show ((modulus d : NNReal) : ℝ) = ‖d‖ from by
            rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p d, coe_nnnorm]]
          push_cast
          rfl

end S_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier (solution)
