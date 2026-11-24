-- Prove2me | solution 1 for GlobalTheory.entire_exists_polynomial_of_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:28.825799+00:00
-- url     : https://prove2.me/submissions/0dcadcf4-f0df-4bec-acf0-2bf56eb980df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_exists_coeff_of_poly_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]
end GlobalTheory
