-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.normSq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:53.967248+00:00
-- url     : https://prove2.me/submissions/f0b6d35b-5bb2-45c6-a4ac-082689fa1c25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber

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
    (hg : gᴴ * sgnMat k * g = sgnMat k) : Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hD : (sgnMat k).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs <;> simp
  have h2 : (Complex.normSq g.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    apply mul_left_cancel₀ hD
    rw [mul_one]
    rw [Complex.star_def] at h
    linear_combination h
  exact_mod_cast h2
end GlobalTheory.HCXi.ConeSlice
