-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6932650f-0910-567c-8ecb-aca76dc2c046

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

private theorem sFinite_selfDualHaarAt_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    SFinite (selfDualHaarAt ℚ v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  infer_instance

private theorem sFinite_mulMeasure_selfDualHaarAt_rat (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ v
    SFinite (mulMeasure (selfDualHaarAt ℚ v)) := by
  letI := localBorel ℚ v
  haveI := sFinite_selfDualHaarAt_rat v
  unfold mulMeasure
  infer_instance

open LanglandsTunnell.CubicInduction in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hν : ∀ i, IsLocallyConstant (ν i))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦl : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hu : ∀ i, ‖(((ν i * χ) (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1)
    (K : ℤ → v.adicCompletion ℚ → v.adicCompletion ℚ → ℂ)
    (hK : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ),
      letI := localBorel ℚ v
      K c a x =
        ∫ p in {p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ |
            Valued.v p.2.1 ≤ WithZero.exp c ∧ Valued.v p.2.2 ≤ WithZero.exp c * Valued.v p.2.1 ∧
              Valued.v (p.1 - p.2.2 / p.2.1) ≤ WithZero.exp c},
          (psiLocal ℚ v (-(p.1 + p.2.1)) : ℂ) *
            cellSectionOf v ν Φ
              (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2 *
                (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
                  (weylPrime3 * transposeInv3 1)) * antidiagonal3 v))
          ∂(jacquetHaar3 v))
    (F : ℤ → v.adicCompletion ℚ → ℂ)
    (hF : ∀ (c : ℤ) (a : (v.adicCompletion ℚ)ˣ),
      letI := localBorel ℚ v
      F c a =
        (∫ x : v.adicCompletion ℚ, K c a x ∂(selfDualHaarAt ℚ v)) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ)⁻¹)
    (c : ℤ) :
    letI := localBorel ℚ v
    localZeta (selfDualHaarAt ℚ v)
        (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 0 * χ)⁻¹ (1 - s) *
      localZeta (selfDualHaarAt ℚ v)
        (fun t => if Valued.v (-t) ≤ WithZero.exp c then (psiLocal ℚ v (-t) : ℂ) else 0) (ν 1 * χ)⁻¹ (1 - s) *
      (∫ p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ,
          Φ ![p.1, p.2.1, p.2.2] *
            (charExt (ν 2 * χ)⁻¹ p.1 * ((modulus p.1 : ℝ) : ℂ) ^ (1 - s)) *
            (charExt (ν 1 * χ) p.2.1 * ((modulus p.2.1 : ℝ) : ℂ) ^ s) *
            (charExt (ν 0 * (ν 1)⁻¹) (p.2.1 - p.1 * p.2.2) *
              ((modulus (p.2.1 - p.1 * p.2.2) : ℝ) : ℂ)⁻¹) *
            (if Valued.v (p.2.2 / (p.2.1 - p.1 * p.2.2)) ≤ WithZero.exp c then
              (psiLocal ℚ v (p.2.2 / (p.2.1 - p.1 * p.2.2)) : ℂ)
            else 0)
        ∂((mulMeasure (selfDualHaarAt ℚ v)).prod
          ((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)))) =
      localZeta (selfDualHaarAt ℚ v) (F c) χ⁻¹ (1 - s) := by
  letI := localBorel ℚ v
  haveI := sFinite_selfDualHaarAt_rat v
  haveI := sFinite_mulMeasure_selfDualHaarAt_rat v
  obtain ⟨-, h2, h3⟩ :=
    LanglandsTunnell.CubicInduction.integrable_and_integral_weight_mul_jacquetWindow_eq_integral_unfolded v ν hν Φ hΦl
      hΦc χ hχ hu s hs hs' K hK c (fun _ _ => (1 : ℂ)) measurable_const 1 (fun _ _ => by simp)
  simp only [one_mul, mul_one] at h2 h3

  have hR : localZeta (selfDualHaarAt ℚ v) (F c) χ⁻¹ (1 - s) =
      ∫ q : v.adicCompletion ℚ × v.adicCompletion ℚ,
        ((modulus q.1 : ℝ) : ℂ)⁻¹ * charExt χ⁻¹ q.1 * ((modulus q.1 : ℝ) : ℂ) ^ (1 - s) * K c q.1 q.2
        ∂((mulMeasure (selfDualHaarAt ℚ v)).prod (selfDualHaarAt ℚ v)) := by
    rw [integral_prod _ h2]
    simp only [localZeta]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    rw [integral_const_mul]
    by_cases ha : a = 0
    · simp [ha]
    · have hFa := hF c (Units.mk0 a ha)
      simp only [Units.val_mk0] at hFa
      rw [hFa]
      ring

  rw [hR, h3]
  simp only [localZeta]
  rw [← integral_prod_mul, ← integral_prod_mul]

end S_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZeta_truncPsi_mul_coupled_eq_localZeta_of_forall_eq_integral_jacquetWindow (solution)
