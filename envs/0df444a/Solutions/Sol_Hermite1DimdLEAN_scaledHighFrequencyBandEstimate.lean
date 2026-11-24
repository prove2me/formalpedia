-- Prove2me | solution 1 for Hermite1DimdLEAN.scaledHighFrequencyBandEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:25.722795+00:00
-- url     : https://prove2.me/submissions/26d13089-e74c-4b85-aa52-0cd2d640a16b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_Hermite1DimdLEAN_highFrequencyBandEstimate
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma circleL2NormSq_const_mul (a : ℂ) (P : Circle → ℂ) :
    circleL2NormSq (fun t => a * P t) = ‖a‖ ^ 2 * circleL2NormSq P := by
  unfold circleL2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [mul_pow]
private lemma circleL2NormSq_real_const_mul (b : ℝ) (f : Circle → ℝ) :
    circleL2NormSq (fun t => b * f t) = b ^ 2 * circleL2NormSq f := by
  unfold circleL2NormSq
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [mul_pow, sq_abs]
private lemma rho_mul_right (a u : ℂ) :
    rho a (a * u) = ‖a‖ * rho 1 u := by
  by_cases ha : a = 0
  · subst ha
    simp [rho]
  · have hnn : 0 ≤ ‖a‖ := norm_nonneg _
    rw [rho, rho]
    have h1 : a + a * u = a * (1 + u) := by ring
    rw [h1, norm_mul]
    calc
      |‖a‖ * ‖1 + u‖ - ‖a‖| = |‖a‖ * (‖1 + u‖ - 1)| := by ring_nf
      _ = ‖a‖ * |‖1 + u‖ - 1| := by rw [abs_mul, abs_of_nonneg hnn]
      _ = ‖a‖ * rho 1 u := by simp [rho]
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (a : ℂ) (N L : ℕ) (P : Circle → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport P N L) :
    circleL2NormSq P ≤ 32 * circleL2NormSq (fun t => rho a (P t)) := by
  by_cases ha : a = 0
  · subst ha
    have hnonneg : 0 ≤ circleL2NormSq P := by
      unfold circleL2NormSq
      positivity
    calc
      circleL2NormSq P ≤ 32 * circleL2NormSq P := by linarith only [hnonneg]
      _ = 32 * circleL2NormSq (fun t => rho 0 (P t)) := by simp [circleL2NormSq, rho]
  · rcases hP with ⟨c, rfl⟩
    let Q : Circle → ℂ := bandLimitedPolynomial N L (fun m => a⁻¹ * c m)
    have hQ : HasBandlimitedSupport Q N L := ⟨fun m => a⁻¹ * c m, rfl⟩
    have hbase := highFrequencyBandEstimate N L (fun m => a⁻¹ * c m) hgap hQ
    have hbaseQ : circleL2NormSq Q ≤ 32 * circleL2NormSq (fun t => rho 1 (Q t)) := by
      exact hbase
    have hmulP : (fun t => a * Q t) = bandLimitedPolynomial N L c := by
      funext t
      simp only [Q, bandLimitedPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      field_simp [ha]
    have hmulR : (fun t => rho a (a * Q t)) = fun t => ‖a‖ * rho 1 (Q t) := by
      funext t
      simp [rho_mul_right]
    rw [← hmulP, circleL2NormSq_const_mul]
    have hconstR :
        circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) =
          ‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t)) :=
      circleL2NormSq_real_const_mul ‖a‖ (fun t => rho 1 (Q t))
    calc
      ‖a‖ ^ 2 * circleL2NormSq Q ≤
          32 * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) :=
            mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖) |>.trans_eq (by ring)
      _ = 32 * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by rw [hconstR]
      _ = 32 * circleL2NormSq (fun t => rho a (a * Q t)) := by rw [hmulR]
end Hermite1DimdLEAN
