-- Prove2me | solution 1 for GlobalTheory.Nef.Kron.ev_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:35.811547+00:00
-- url     : https://prove2.me/submissions/4c59ee63-e189-4611-be7e-360d0aaa5d1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
import Theorems.Thm_GlobalTheory_Nef_Kron_ev_monomial
import Theorems.Thm_GlobalTheory_Nef_Kron_ev_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)
namespace GlobalTheory.Nef.Kron
theorem _root_.solution (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by
  rw [mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]
end GlobalTheory.Nef.Kron
