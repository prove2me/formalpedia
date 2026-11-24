-- Prove2me | solution 1 for HermitekLEAN.finiteCirclePoly_support_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:12.72282+00:00
-- url     : https://prove2.me/submissions/ef77aa55-7ad4-4ad7-9479-eec193eb6cfd

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k D : ℕ} (r : ℝ) (a : Fin (D + 1) → ℂ),
      a 0 = 0 →
        finiteCirclePoly k r a =
          positiveTrigonometricPolynomial (frequencyBand 1 D) (finiteCircleCoeff k r a) := by
  intro k D r a h0
  ext t
  have hband : frequencyBand 0 (D + 1) = insert 0 (frequencyBand 1 D) := by
    simpa only [HermiteLEAN.frequencyBand, zero_add, add_tsub_cancel_right, add_tsub_cancel_left,
      Nat.succ_eq_add_one, Nat.succ_sub_one] using
      (Finset.insert_Icc_add_one_left_eq_Icc (a := (0 : ℕ)) (b := D) (by omega)).symm
  change
    Finset.sum (frequencyBand 0 (D + 1)) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t) =
      Finset.sum (frequencyBand 1 D) (fun n => finiteCircleCoeff k r a n * fourier (n : ℤ) t)
  rw [hband, Finset.sum_insert]
  · simp [finiteCircleCoeff, h0]
  · simp [HermiteLEAN.frequencyBand]
end HermitekLEAN
