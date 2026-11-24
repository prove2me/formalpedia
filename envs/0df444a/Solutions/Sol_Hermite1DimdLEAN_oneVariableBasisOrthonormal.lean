-- Prove2me | solution 1 for Hermite1DimdLEAN.oneVariableBasisOrthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:57.491844+00:00
-- url     : https://prove2.me/submissions/e86d7315-9f7f-44dd-b3b2-40115fc1abdc

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_phi_orthonormal
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma measurable_ofReal_gaussianDensity (d : ℕ) :
    Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) := by
  unfold gaussianDensity
  fun_prop
private lemma gaussianDensity_ofReal_lt_top (d : ℕ) :
    ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ := by
  simp_all
private lemma toReal_gaussianDensity_one (z : CSpace 1) :
    (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
      (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
  have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by positivity
  simp [gaussianDensity, hnonneg]
private lemma integral_funUnique_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℂ → E) :
    ∫ z : CSpace 1, φ (z 0) ∂(volume : Measure (CSpace 1)) =
      ∫ z : ℂ, φ z ∂(volume : Measure ℂ) := by
  have hEq0 :=
    ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (f := MeasurableEquiv.funUnique (Fin 1) ℂ) φ)
  exact hEq0
private theorem gaussianInner_oneDimPhi_eq_weightedInner
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n) := by
  change
    gaussianInner (d := 1) (fun z => HermitekLEAN.Phi k m (z 0))
      (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.weightedInner (HermitekLEAN.Phi k m) (HermitekLEAN.Phi k n)
  unfold gaussianInner HermitekLEAN.weightedInner HermiteLEAN.weightedInner
  rw [gaussianMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)]
  have hcomp :
        ∫ z : CSpace 1,
            HermitekLEAN.Phi k m (z 0) *
              ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0)))
              ∂(volume : Measure (CSpace 1)) =
          ∫ z : ℂ,
            HermitekLEAN.Phi k m z *
              ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z))
              ∂(volume : Measure ℂ) :=
    integral_funUnique_one (fun z : ℂ =>
      HermitekLEAN.Phi k m z * ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n z)))
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0)))
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi : ℂ) *
          ((HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ))) ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Algebra.smul_def, toReal_gaussianDensity_one z,
            show (algebraMap ℝ ℂ) ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) =
                ((1 / Real.pi : ℂ) * (Real.exp (-‖z 0‖ ^ 2) : ℂ)) by simp]
          ring
    _ =
      (1 / Real.pi : ℂ) *
        ∫ z : CSpace 1,
          (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
            (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) :=
            MeasureTheory.integral_const_mul _ _
    _ = (1 / Real.pi : ℂ) *
        ∫ z : ℂ,
          (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
            (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
          have hcomp' : ∫ z : CSpace 1,
              (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                (Real.exp (-‖z 0‖ ^ 2) : ℂ) ∂(volume : Measure (CSpace 1)) =
              ∫ z : ℂ,
                (HermitekLEAN.Phi k m z * conj (HermitekLEAN.Phi k n z)) *
                  (Real.exp (-‖z‖ ^ 2) : ℂ) ∂(volume : Measure ℂ) := by
            rw [show (fun z : CSpace 1 =>
                  (HermitekLEAN.Phi k m (z 0) * conj (HermitekLEAN.Phi k n (z 0))) *
                    (Real.exp (-‖z 0‖ ^ 2) : ℂ)) =
                fun z : CSpace 1 =>
                  HermitekLEAN.Phi k m (z 0) *
                    ((Real.exp (-‖z 0‖ ^ 2) : ℂ) * conj (HermitekLEAN.Phi k n (z 0))) from
                by funext z; ring,
              hcomp]
            apply integral_congr_ae
            filter_upwards with z
            ring
          rw [hcomp']
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
    (k m n : ℕ) :
    gaussianInner (d := 1) (oneDimLift (oneDimPhi k m)) (oneDimLift (oneDimPhi k n)) =
      if m = n then (1 : ℂ) else 0 := by
  /-
  Scaffolding guidance:
  re-export the frozen one-dimensional basis theorem under a stable name.
  Downstream files only use orthonormality and finite Parseval consequences.
  -/
  rw [gaussianInner_oneDimPhi_eq_weightedInner]
  exact (HermitekLEAN.phi_orthonormal (k := k) (m := m) (n := n))
end Hermite1DimdLEAN
