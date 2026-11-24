-- Prove2me | solution 1 for Hermite1DimdLEAN.scaledPositiveFrequencyCircleEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:00.150738+00:00
-- url     : https://prove2.me/submissions/a058da23-04d3-4d15-8fe5-f38283e6a330

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_Hermite1DimdLEAN_positiveFrequencyCircleEstimate
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
    (a : ℂ) (E : Finset ℕ) (P : Circle → ℂ)
    (hpos : ∀ n ∈ E, 0 < n)
    (hP : HasPositiveFrequencySupport P E) :
    circleL2NormSq P ≤ 144 * E.card * circleL2NormSq (fun t => rho a (P t)) := by
  /-
  Scaffolding guidance:
  normalize by `a` when `a ≠ 0`, and keep the `a = 0` branch separate.
  Export the final statement so later files do not redo the rescaling.
  -/
  by_cases ha : a = 0
  · subst ha
    rcases hP with ⟨b, rfl⟩
    by_cases hE : E = ∅
    · subst hE
      simp [positiveFrequencyPolynomial, circleL2NormSq, rho]
    · have hnonneg : 0 ≤ circleL2NormSq (positiveFrequencyPolynomial E b) := by
        unfold circleL2NormSq
        positivity
      have hcard : 0 < E.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
      have honeR : (1 : ℝ) ≤ E.card := by exact_mod_cast (Nat.succ_le_of_lt hcard)
      have hfac : (1 : ℝ) ≤ 144 * (E.card : ℝ) := by linarith only [honeR]
      calc
        circleL2NormSq (positiveFrequencyPolynomial E b)
            ≤ 144 * E.card * circleL2NormSq (positiveFrequencyPolynomial E b) :=
              le_mul_of_one_le_left hnonneg hfac
        _ =
          144 * E.card *
            circleL2NormSq (fun t => rho 0 (positiveFrequencyPolynomial E b t)) := by
              simp [circleL2NormSq, rho]
  · rcases hP with ⟨b, rfl⟩
    let Q : Circle → ℂ := positiveFrequencyPolynomial E (fun n => a⁻¹ * b n)
    have hQ : HasPositiveFrequencySupport Q E := ⟨fun n => a⁻¹ * b n, rfl⟩
    have hbase :=
      positiveFrequencyCircleEstimate E (fun n => a⁻¹ * b n) hpos hQ
    have hbaseQ :
        circleL2NormSq Q ≤
          144 * E.card * circleL2NormSq (fun t => rho 1 (Q t)) := by exact hbase
    have hmulP : (fun t => a * Q t) = positiveFrequencyPolynomial E b := by
      funext t
      simp only [Q, positiveFrequencyPolynomial, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro n hn
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
          144 * E.card * (‖a‖ ^ 2 * circleL2NormSq (fun t => rho 1 (Q t))) := by
            have hscaled := mul_le_mul_of_nonneg_left hbaseQ (sq_nonneg ‖a‖)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
      _ = 144 * E.card * circleL2NormSq (fun t => ‖a‖ * rho 1 (Q t)) := by rw [hconstR]
      _ = 144 * E.card * circleL2NormSq (fun t => rho a (a * Q t)) := by rw [hmulR]
end Hermite1DimdLEAN
