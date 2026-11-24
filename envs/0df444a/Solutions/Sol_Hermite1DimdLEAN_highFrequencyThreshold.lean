-- Prove2me | solution 1 for Hermite1DimdLEAN.highFrequencyThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:34.465023+00:00
-- url     : https://prove2.me/submissions/911ff4f5-646e-4a61-8afb-e2c0c99adf5d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_DegreeBookkeeping
public import Theorems.Thm_Hermite1DimdLEAN_highAnnulusDegreeBounds
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    {d : ℕ} (hd : 1 ≤ d) (j : MultiIndex d) (M : ℕ)
    (hj : degreeThreshold d M ≤ annulusRadius j) :
    1343 * (degreeWidth j M) ^ 2 ≤ (degreeIntervalLower j M) ^ 2 := by
  /-
  Scaffolding guidance:
  prove this numerically once the crude growth estimates are frozen.
  The imported high-frequency theorem uses the exact constant `1343`.
  -/
  let R := annulusRadius j
  let x := R - M
  have hM1 : M + 1 ≤ degreeThreshold d M := by
    unfold degreeThreshold
    have hdpos : 0 < d := by omega
    have hodd : 0 < 2 * M + 1 := by omega
    have hprod : 0 < 120 * d * (2 * M + 1) := Nat.mul_pos (Nat.mul_pos (by decide) hdpos) hodd
    omega
  have hhigh' : M + 1 ≤ annulusRadius j := le_trans hM1 hj
  have hhigh : M + 1 ≤ R := by exact hhigh'
  rcases highAnnulusDegreeBounds (hd := hd) (j := j) (M := M) hhigh with ⟨hlower, hwidth⟩
  have hx_ge : 120 * d * (2 * M + 1) ≤ x := by
    dsimp [x, R]
    unfold degreeThreshold at hj
    omega
  have hM_bound : 2 * M + 1 ≤ x := by
    have h1 : 2 * M + 1 ≤ 120 * d * (2 * M + 1) := by nlinarith only [hd]
    exact le_trans h1 hx_ge
  have hR_bound : 2 * R + 1 ≤ 3 * x := by
    dsimp [x]
    omega
  have h40base : 40 * d * (2 * M + 1) * (2 * R + 1) ≤ x * x := by
    have hstep1 :
        40 * d * (2 * M + 1) * (2 * R + 1) ≤ 40 * d * (2 * M + 1) * (3 * x) := by gcongr
    have hstep2 : 40 * d * (2 * M + 1) * (3 * x) = (120 * d * (2 * M + 1)) * x := by ring
    have hstep3 : (120 * d * (2 * M + 1)) * x ≤ x * x := by exact Nat.mul_le_mul_right x hx_ge
    calc
      40 * d * (2 * M + 1) * (2 * R + 1) ≤ 40 * d * (2 * M + 1) * (3 * x) := hstep1
      _ = (120 * d * (2 * M + 1)) * x := hstep2
      _ ≤ x * x := hstep3
  have h40 : 40 * degreeWidth j M ≤ x * x := by
    have hmul : 40 * degreeWidth j M ≤ 40 * (d * (2 * M + 1) * (2 * R + 1)) :=
      Nat.mul_le_mul_left 40 (by exact hwidth)
    exact le_trans hmul (by simpa [mul_assoc] using h40base)
  have h1600 : 1600 * (degreeWidth j M) ^ 2 ≤ x ^ 4 := by
    have hsq := Nat.mul_self_le_mul_self h40
    simpa [pow_two, pow_succ, x, mul_assoc, mul_left_comm, mul_comm] using hsq
  have h1343 : 1343 * (degreeWidth j M) ^ 2 ≤ x ^ 4 :=
    le_trans (Nat.mul_le_mul_right ((degreeWidth j M) ^ 2) (by decide : 1343 ≤ 1600)) h1600
  have hlower_sq : x ^ 4 ≤ (degreeIntervalLower j M) ^ 2 := by
    have hsq := Nat.mul_self_le_mul_self (by exact hlower)
    simpa [pow_two, pow_succ, x, mul_assoc, mul_left_comm, mul_comm] using hsq
  exact le_trans h1343 hlower_sq
end Hermite1DimdLEAN
