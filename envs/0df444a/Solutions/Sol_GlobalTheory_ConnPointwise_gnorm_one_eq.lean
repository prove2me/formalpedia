-- Prove2me | solution 1 for GlobalTheory.ConnPointwise.gnorm_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:32.085706+00:00
-- url     : https://prove2.me/submissions/b0cd4b54-dfc5-42b3-b6f1-35f2435bfd7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
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
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.ConnPointwise
variable {g : ℕ}
namespace GlobalTheory.ConnPointwise
theorem _root_.solution (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]
end GlobalTheory.ConnPointwise
