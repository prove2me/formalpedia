-- Prove2me | solution 1 for HairerSPDE.cameronMartinNorm_of_covariance_repr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:40:11.742909+00:00
-- url     : https://prove2.me/submissions/677d8f71-372c-419b-8bd7-3f64c11aed2e

import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HairerSPDE

theorem cameronMartinNormOfCovarianceReprProof
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B, covarianceBilinDual μ h' L = L h) :
    cameronMartinNorm μ h =
      ENNReal.ofReal (Real.sqrt (covarianceBilinDual μ h' h')) := by
  let q : ℝ := covarianceBilinDual μ h' h'
  have hq : 0 ≤ q := covarianceBilinDual_self_nonneg h'
  have hupper : cameronMartinNorm μ h ≤ ENNReal.ofReal (Real.sqrt q) := by
    refine iSup_le fun L => ?_
    have hcs : (covarianceBilinDual μ h' (L : StrongDual ℝ B)) ^ 2 ≤
        covarianceBilinDual μ h' h' *
          covarianceBilinDual μ (L : StrongDual ℝ B) (L : StrongDual ℝ B) := by
      exact (covarianceBilinDual μ).toBilinForm.apply_sq_le_of_symm
        (fun M => covarianceBilinDual_self_nonneg M)
        (LinearMap.BilinForm.isSymm_iff.mp
          (isPosSemidef_covarianceBilinDual (μ := μ)).isSymm) h' L
    have hsq : ((L : StrongDual ℝ B) h) ^ 2 ≤ q := by
      rw [← hh' L]
      calc
        (covarianceBilinDual μ h' (L : StrongDual ℝ B)) ^ 2 ≤
            covarianceBilinDual μ h' h' *
              covarianceBilinDual μ (L : StrongDual ℝ B) (L : StrongDual ℝ B) := hcs
        _ ≤ q * 1 := by
          dsimp [q]
          exact mul_le_mul_of_nonneg_left L.property hq
        _ = q := mul_one q
    have hle : (L : StrongDual ℝ B) h ≤ Real.sqrt q := by
      nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
    exact ENNReal.ofReal_le_ofReal hle
  apply le_antisymm hupper
  by_cases hq0 : q = 0
  · simp [hq0]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.2 hqpos
    let a : ℝ := (Real.sqrt q)⁻¹
    have hscaled : covarianceBilinDual μ (a • h') (a • h') ≤ 1 := by
      simp only [map_smul, smul_eq_mul]
      change a * (a * q) ≤ 1
      dsimp [a]
      field_simp [hsqrt.ne']
      nlinarith [Real.sq_sqrt hq]
    have hval : (a • h') h = Real.sqrt q := by
      calc
        (a • h') h = a * h' h := by simp
        _ = a * q := by rw [← hh' h']
        _ = Real.sqrt q := by
          dsimp [a]
          field_simp [hsqrt.ne']
          nlinarith [Real.sq_sqrt hq]
    calc
      ENNReal.ofReal (Real.sqrt q) = ENNReal.ofReal ((a • h') h) := by rw [hval]
      _ ≤ cameronMartinNorm μ h := by
        exact le_iSup
          (fun L : {L : StrongDual ℝ B // covarianceBilinDual μ L L ≤ 1} =>
            ENNReal.ofReal ((L : StrongDual ℝ B) h))
          ⟨a • h', hscaled⟩

end HairerSPDE

theorem solution
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B,
      covarianceBilinDual μ h' L = L h) :
    HairerSPDE.cameronMartinNorm μ h =
      ENNReal.ofReal (Real.sqrt (covarianceBilinDual μ h' h')) := by
  exact HairerSPDE.cameronMartinNormOfCovarianceReprProof μ hμ h h' hh'
