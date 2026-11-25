-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.form_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:35.297802+00:00
-- url     : https://prove2.me/submissions/0579d5cc-23e2-4540-8dbb-f304e470c115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_form_eq

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
    (hg : gᴴ * sgnMat k * g = sgnMat k) (v : Fin (k + 1) → ℂ) :
    Complex.normSq ((g *ᵥ v) (Fin.last k)) - sqLen (Fin.init (g *ᵥ v) : Fin k → ℂ) =
      Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ) := by
  have h : star (g *ᵥ v) ⬝ᵥ (sgnMat k *ᵥ (g *ᵥ v)) = star v ⬝ᵥ (sgnMat k *ᵥ v) := by
    conv_rhs => rw [← hg]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [form_eq, form_eq, Complex.ofReal_inj] at h
  linarith
end GlobalTheory.HCXi.ConeSlice
