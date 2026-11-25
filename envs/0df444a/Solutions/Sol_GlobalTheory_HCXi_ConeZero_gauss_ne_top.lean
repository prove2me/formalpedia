-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.gauss_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:59.767259+00:00
-- url     : https://prove2.me/submissions/492d4d71-4d45-443c-a6d2-dc56528a4850

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure

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
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution (n : ℕ) :
    ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (Real.exp (-(2 * sqLen w))) ≠ ∞ := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-(2 * Complex.normSq z))) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 2)
      (by norm_num) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp, Complex.normSq_eq_norm_sq]
    congr 1
    rw [← Complex.ofReal_pow]
    simp [-Complex.ofReal_pow]
  have h2 : Integrable (fun w : Fin n → ℂ => ∏ i, Real.exp (-(2 * Complex.normSq (w i)))) :=
    Integrable.fintype_prod (f := fun _ z => Real.exp (-(2 * Complex.normSq z))) fun _ => h1
  have h3 : Integrable (fun w : Fin n → ℂ => Real.exp (-(2 * sqLen w))) := by
    refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [sqLen, ← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  exact h3.lintegral_lt_top.ne
end GlobalTheory.HCXi.ConeZero
