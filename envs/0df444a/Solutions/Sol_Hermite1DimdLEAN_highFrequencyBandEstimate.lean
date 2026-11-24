-- Prove2me | solution 1 for Hermite1DimdLEAN.highFrequencyBandEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:27.1286+00:00
-- url     : https://prove2.me/submissions/41366bf8-58bc-4b63-a6eb-f32d735586eb

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_HermiteLEAN_high_frequency_circle_estimate
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_high_frequency_circle_estimate
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.1) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    simp_all
  · simp_all
private theorem positiveBandEq (N L : ℕ) (hL : 1 ≤ L) (c : Fin L → ℂ) :
    HermiteLEAN.positiveTrigonometricPolynomial
        (HermiteLEAN.frequencyBand N L) (bandCoeff N L c) =
      bandLimitedPolynomial N L c := by
  ext t
  rw [HermiteLEAN.positiveTrigonometricPolynomial, HermiteLEAN.frequencyBand,
    sum_Icc_eq_sum_Fin N L hL]
  simp [bandLimitedPolynomial, bandCoeff]
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
    (N L : ℕ) (c : Fin L → ℂ)
    (hgap : 1343 * L ^ 2 ≤ N ^ 2)
    (hP : HasBandlimitedSupport (bandLimitedPolynomial N L c) N L) :
    circleL2NormSq (bandLimitedPolynomial N L c) ≤
      32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
  /-
  Scaffolding guidance:
  this is the band-limited estimate used after the degree-threshold argument.
  Preserve the exact constants and the separate support hypothesis.
  -/
  by_cases hL0 : L = 0
  · subst hL0
    simp only [circleL2NormSq, bandLimitedPolynomial, univ_eq_empty, Nat.cast_add, fourier_apply,
      fourier_add', natCast_zsmul, sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, norm_eq_abs, sq_abs, integral_const,
      probReal_univ, smul_eq_mul, one_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  · have hL : 1 ≤ L := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hL0)
    have hNsqpos : 0 < N ^ 2 := lt_of_lt_of_le (by positivity) hgap
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hNsqpos
    have hBandEq := positiveBandEq N L hL c
    calc
      circleL2NormSq (bandLimitedPolynomial N L c)
          = HermiteLEAN.circleL2Sq
              (HermiteLEAN.positiveTrigonometricPolynomial
                (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            rw [hBandEq]
            rfl
      _ ≤ 32 * HermiteLEAN.circleRhoNormSq
            (HermiteLEAN.positiveTrigonometricPolynomial
              (HermiteLEAN.frequencyBand N L) (bandCoeff N L c)) := by
            have hgap_real : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgap
            simpa using
              HermitekLEAN.high_frequency_circle_estimate N L hN hL (bandCoeff N L c)
                hgap_real
      _ = 32 * circleL2NormSq (fun t => rho 1 (bandLimitedPolynomial N L c t)) := by
            rw [hBandEq]
            simp [circleL2NormSq, rho, HermiteLEAN.circleRhoNormSq, HermiteLEAN.rho,
              sq_abs]
end Hermite1DimdLEAN
