-- Prove2me | solution 1 for HermitekLEAN.truncate_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:36.36539+00:00
-- url     : https://prove2.me/submissions/594e6f66-babe-4a9e-af85-e6a1284b093a

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion
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
    ∀ {k J : ℕ} {G H : ℂ → ℂ},
      H ∈ Hk k →
        (∀ n : ℕ,
          hermiteCoeff k H n = if _h : n < J + 1 then hermiteCoeff k G n else 0) →
            H = truncate k J G := by
  intro k J G H hH hcoeffs
  have hexp := hermiteCoeff_expansion hH
  rw [hexp]
  ext z
  simp only [hermiteSeries, truncate, finiteHermiteSum]
  rw [show (∑' n : ℕ, hermiteCoeff k H n * Phi k n z) =
    ∑ n ∈ Finset.range (J + 1), hermiteCoeff k H n * Phi k n z from by
      apply tsum_eq_sum
      intro n hn
      rw [Finset.mem_range] at hn
      rw [hcoeffs n, dif_neg hn, zero_mul]]
  rw [Finset.sum_range]
  congr 1
  ext ⟨n, hn⟩
  simp only []
  rw [hcoeffs n, dif_pos hn]
end HermitekLEAN
