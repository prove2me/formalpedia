-- Prove2me | solution 1 for GlobalTheory.mem_germIdeal_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:32.4478+00:00
-- url     : https://prove2.me/submissions/2fcd23fd-3d3f-4bf1-b583-634c1d14d19e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_X_mem_germIdeal
import Theorems.Thm_GlobalTheory_exists_eq_sum_X_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] GlobalTheory.constDerivEval_X

set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ ∀ d : σ →₀ ℕ, degree d < n → coeff d g = 0 := by
  cases nonempty_fintype σ
  constructor
  · intro hg
    suffices h : (n : ℕ∞) ≤ g.order from fun d hd =>
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)
    induction n generalizing g with
    | zero => simp
    | succ n ih =>
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · refine le_trans ?_ le_order_mul
        push_cast
        refine add_le_add (ih ha) ?_
        exact_mod_cast nat_le_order (n := 1) fun d hd => by
          obtain rfl : d = 0 := by simpa [degree_eq_zero_iff] using hd
          simpa using hb
      · exact (le_min ha hb).trans min_order_le_add
  · induction n generalizing g with
    | zero => simp
    | succ n ih =>
      intro hg
      obtain ⟨h, hh, rfl⟩ := exists_eq_sum_X_mul hg
      rw [pow_succ']
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (X_mem_germIdeal i) (ih (hh i))
end GlobalTheory
