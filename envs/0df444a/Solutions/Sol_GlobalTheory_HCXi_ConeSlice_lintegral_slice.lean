-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.lintegral_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:28:34.754548+00:00
-- url     : https://prove2.me/submissions/8a92e721-a729-4634-af16-d16a4fe1c09f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_sqLen
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_form_inv
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_normSq_det
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_mulVec
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_measurePreserving_mulVec
import Theorems.Thm_GlobalTheory_T_lintegral_hyperboloid_fibration


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeSlice
namespace GlobalTheory.HCXi.ConeSlice
theorem _root_.solution {k : ℕ} {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hg : gᴴ * sgnMat k * g = sgnMat k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ τ in Set.Ioi 0, F τ * slice g τ = ∫⁻ τ in Set.Ioi 0, F τ * slice (k := k) 1 τ := by
  have hψ : Continuous (fun v : Fin (k + 1) → ℂ => ENNReal.ofReal (Real.exp (-sqLen v))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp continuous_sqLen.neg)
  have hQ : Continuous (fun v : Fin (k + 1) → ℂ =>
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) :=
    (Complex.continuous_normSq.comp (continuous_apply _)).sub
      (continuous_sqLen.comp (continuous_pi fun i => continuous_apply _))
  have h1 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F (hψ.comp (continuous_mulVec g)).measurable hF
  have h2 := GlobalTheory.T.lintegral_hyperboloid_fibration k _ F hψ.measurable hF
  have hset : {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      = {v | 0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} := by
    ext v; simp
  have hS : MeasurableSet {v : Fin (k + 1) → ℂ |
      0 < Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)} :=
    (isOpen_lt continuous_const hQ).measurableSet
  have h3 := (measurePreserving_mulVec (normSq_det hg)).setLIntegral_comp_preimage hS
    (f := fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) *
      ENNReal.ofReal (Real.exp (-sqLen v))) ((hF.comp hQ.measurable).mul hψ.measurable)
  simp only [Set.preimage_setOf_eq, form_inv hg] at h3
  rw [hset] at h1 h2
  simp only [Function.comp_apply] at h1
  rw [h3, h2] at h1
  have h4 := (ENNReal.mul_right_inj (by simp) (by simp)).1 h1
  simp only [slice, Matrix.one_mulVec]
  exact h4.symm
end GlobalTheory.HCXi.ConeSlice
