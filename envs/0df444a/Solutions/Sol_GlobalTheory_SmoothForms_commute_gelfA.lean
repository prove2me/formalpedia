-- Prove2me | solution 1 for GlobalTheory.SmoothForms.commute_gelfA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:21:13.417796+00:00
-- url     : https://prove2.me/submissions/64e50f97-c7d8-4bdb-ad07-dde67989acbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PowEntryCommutator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Theorems.Thm_GlobalTheory_SmoothForms_gelfA_eq_sum_pow
import Theorems.Thm_GlobalTheory_SmoothForms_comm_pow_of_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E → ∀ (k : ℕ) (a b : Fin n), E a b * gelfA E k = gelfA E k * E a b := by
  intro A _ _ n E hE k a b
  rw [← sub_eq_zero, gelfA_eq_sum_pow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]
end GlobalTheory.SmoothForms
