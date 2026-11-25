-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.integrable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:06.622624+00:00
-- url     : https://prove2.me/submissions/f78e2c86-8b1a-42ac-a5aa-8a5392fc131c

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
theorem _root_.solution {k : ℕ} {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : Fin k → ℂ => Real.exp (-(c * sqLen w))) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(c * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ))
      (by simpa using hc) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    simp [← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin k) (f := fun _ (z : ℂ) => Real.exp (-(c * Complex.normSq z)))
    (μ := fun _ => volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
end GlobalTheory.HCXi.ConeSlice
