-- Prove2me | solution 1 for HermitekLEAN.finiteHermiteSum_normSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:19.916874+00:00
-- url     : https://prove2.me/submissions/4e1ba963-aa0f-4b6a-b2f8-bedb3a753dd8

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_inner
attribute [local simp] HermitekLEAN.qkn_real
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma weightedNormSq_eq_re_weightedInner (F : ℂ → ℂ) :
    weightedNormSq F = Complex.re (weightedInner F F) := by
  unfold HermitekLEAN.weightedNormSq HermiteLEAN.weightedNormSq
  unfold HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  have hfun :
      (fun z : ℂ => F z * (starRingEnd ℂ) (F z) * (Real.exp (-‖z‖ ^ 2) : ℂ))
        = fun z : ℂ => ((‖F z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
    funext z
    rw [show F z * (starRingEnd ℂ) (F z) = ((‖F z‖ ^ 2 : ℝ) : ℂ) by
      simpa only [ofReal_pow] using Complex.mul_conj' (F z)]
    simp
  rw [hfun, integral_complex_ofReal]
  simp
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k D : ℕ} (a : Fin D → ℂ),
      weightedNormSq (finiteHermiteSum k a) = ∑ n : Fin D, ‖a n‖ ^ 2 := by
  intro k D a
  rw [weightedNormSq_eq_re_weightedInner, finiteHermiteSum_inner]
  simp [Complex.normSq, Complex.sq_norm]
end HermitekLEAN
