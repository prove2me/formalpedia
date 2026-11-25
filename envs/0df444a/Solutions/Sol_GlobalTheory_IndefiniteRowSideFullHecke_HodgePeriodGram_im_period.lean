-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:27.581903+00:00
-- url     : https://prove2.me/submissions/cee04579-cd79-4a4b-b9da-1e6d74c6dcb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
open Matrix Complex Filter Topology
open scoped ComplexOrder
variable {n a g : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
theorem _root_.solution (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by
  ext j k
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.add_im, Complex.im_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL i, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Complex.norm_exp, Real.log_exp]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Complex.mul_im, Complex.div_re, Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
