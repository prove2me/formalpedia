-- Prove2me | solution 1 for HermitekLEAN.integrable_weightedDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:02:26.60869+00:00
-- url     : https://prove2.me/submissions/c76d68a2-5c9d-43c9-9ed0-121d6aa49e7c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_phi_orthonormal
attribute [local simp] HermitekLEAN.qkn_real

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution (k n : ℕ) :
    Integrable (fun z : ℂ => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) := by
  let f : ℂ → ℝ := fun z => ‖Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
  by_contra hf
  have hfC : ¬ Integrable (fun z : ℂ => (f z : ℂ)) := by
    intro hC
    have hre : (fun z : ℂ => ((f z : ℂ)).re) = f := funext fun z => Complex.ofReal_re (f z)
    exact hf (hre ▸ hC.re)
  have hzero : weightedInner (Phi k n) (Phi k n) = 0 := by
    unfold weightedInner HermiteLEAN.weightedInner
    calc
      (1 / Real.pi : ℂ) *
          ∫ z : ℂ, Phi k n z * (starRingEnd ℂ) (Phi k n z) * (Real.exp (-‖z‖ ^ 2) : ℂ)
        = (1 / Real.pi : ℂ) * ∫ z : ℂ, (f z : ℂ) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with z
            rw [mul_conj]
            simp [f, Complex.normSq_eq_norm_sq]
      _ = (1 / Real.pi : ℂ) * 0 := by rw [MeasureTheory.integral_undef hfC]
      _ = 0 := by ring
  have hone : weightedInner (Phi k n) (Phi k n) = 1 := by
    simpa only [↓reduceIte] using (phi_orthonormal (k := k) (m := n) (n := n))
  simp_all only [one_ne_zero]
end HermitekLEAN
