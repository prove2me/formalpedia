-- Prove2me | solution 1 for HairerSPDE.norm_le_cameronMartinNorm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T16:36:33.964207+00:00
-- url     : https://prove2.me/submissions/a532bd42-463f-493e-ab16-452f483c3993

import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HairerSPDE

theorem normLeCameronMartinNormProof
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (C : ℝ)
    (hC : ∀ L₁ L₂ : StrongDual ℝ B,
      covarianceBilinDual μ L₁ L₂ ≤ C * ‖L₁‖ * ‖L₂‖)
    (h : B) (r : ℝ≥0) (hr : cameronMartinNorm μ h ≤ r) :
    ‖h‖ ≤ Real.sqrt C * r := by
  obtain ⟨L, hLnorm, hLh⟩ := exists_dual_vector'' ℝ h
  by_cases hC0 : C ≤ 0
  · have hcov0 : covarianceBilinDual μ L L = 0 := by
      apply le_antisymm
      · calc
          covarianceBilinDual μ L L ≤ C * ‖L‖ * ‖L‖ := hC L L
          _ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg hC0 (norm_nonneg L))
              (norm_nonneg L)
      · exact covarianceBilinDual_self_nonneg L
    have hscaled (a : ℝ) : covarianceBilinDual μ (a • L) (a • L) ≤ 1 := by
      simp [hcov0]
    have hval (a : ℝ) : ENNReal.ofReal ((a • L) h) ≤ (r : ℝ≥0∞) := by
      calc
        ENNReal.ofReal ((a • L) h) ≤ cameronMartinNorm μ h := by
          exact le_iSup (fun Q : {Q : StrongDual ℝ B //
            covarianceBilinDual μ Q Q ≤ 1} => ENNReal.ofReal ((Q : StrongDual ℝ B) h))
            ⟨a • L, hscaled a⟩
        _ ≤ r := hr
    have hzero : ‖h‖ = 0 := by
      by_contra hh
      have hp : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hh)
      let a : ℝ := (r : ℝ) / ‖h‖ + 1
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have haval : a * ‖h‖ ≤ (r : ℝ) := by
        have := (ENNReal.ofReal_le_coe).mp (hval a)
        simpa [ContinuousLinearMap.smul_apply, hLh, ENNReal.coe_toNNReal] using this
      dsimp [a] at haval
      field_simp [ne_of_gt hp] at haval
      linarith
    simp [hzero, Real.sqrt_eq_zero_of_nonpos hC0]
  · have hCpos : 0 < C := lt_of_not_ge hC0
    let a : ℝ := (Real.sqrt C)⁻¹
    have hsqrt : 0 < Real.sqrt C := Real.sqrt_pos.2 hCpos
    have hcov : covarianceBilinDual μ (a • L) (a • L) ≤ 1 := by
      calc
        covarianceBilinDual μ (a • L) (a • L)
            ≤ C * ‖a • L‖ * ‖a • L‖ := hC _ _
        _ ≤ C * |a| * |a| := by
          simp only [norm_smul, Real.norm_eq_abs]
          have haL : |a| * ‖L‖ ≤ |a| := by
            simpa using mul_le_mul_of_nonneg_left hLnorm (abs_nonneg a)
          have hsquare : (|a| * ‖L‖) * (|a| * ‖L‖) ≤ |a| * |a| :=
            mul_le_mul haL haL (mul_nonneg (abs_nonneg a) (norm_nonneg L))
              (abs_nonneg a)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsquare hCpos.le
        _ = 1 := by
          dsimp [a]
          rw [abs_inv, abs_of_pos hsqrt]
          field_simp [hsqrt.ne']
          nlinarith [Real.sq_sqrt hCpos.le]
    have hval : ENNReal.ofReal ((a • L) h) ≤ (r : ℝ≥0∞) := by
      calc
        ENNReal.ofReal ((a • L) h) ≤ cameronMartinNorm μ h := by
          exact le_iSup (fun Q : {Q : StrongDual ℝ B //
            covarianceBilinDual μ Q Q ≤ 1} => ENNReal.ofReal ((Q : StrongDual ℝ B) h))
            ⟨a • L, hcov⟩
        _ ≤ r := hr
    have hreal : a * ‖h‖ ≤ (r : ℝ) := by
      have := (ENNReal.ofReal_le_coe).mp hval
      simpa [ContinuousLinearMap.smul_apply, hLh, ENNReal.coe_toNNReal,
        mul_nonneg hsqrt.le (norm_nonneg h)] using this
    dsimp [a] at hreal
    have := (inv_mul_le_iff₀ hsqrt).mp hreal
    simpa [mul_comm] using this

end HairerSPDE

theorem solution
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (C : ℝ)
    (hC : ∀ L₁ L₂ : StrongDual ℝ B,
      covarianceBilinDual μ L₁ L₂ ≤ C * ‖L₁‖ * ‖L₂‖)
    (h : B) (r : ℝ≥0) (hr : HairerSPDE.cameronMartinNorm μ h ≤ r) :
    ‖h‖ ≤ Real.sqrt C * r := by
  exact HairerSPDE.normLeCameronMartinNormProof μ hμ C hC h r hr
