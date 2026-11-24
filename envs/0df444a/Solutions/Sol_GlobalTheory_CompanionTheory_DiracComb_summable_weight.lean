-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DiracComb.summable_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:25:46.522804+00:00
-- url     : https://prove2.me/submissions/3fa65707-596c-4a3a-a0cb-dcc179aa0ebc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb
namespace GlobalTheory.CompanionTheory.DiracComb
theorem _root_.solution (n : ℕ) :
    Summable fun m : Fin n → ℤ => ((1 + ‖(fun i => (m i : ℝ))‖) ^ (2 * n))⁻¹ := by
  have h1 : Summable fun k : ℤ => ((1 + |(k : ℝ)|) ^ 2)⁻¹ := by
    refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.2 (by norm_num : 1 < 2)) ?_
    filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
    have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (by exact_mod_cast hk)
    rw [Real.norm_of_nonneg (by positivity), one_div, ← sq_abs (k : ℝ)]
    gcongr
    linarith
  have h2 : ∀ n : ℕ, Summable fun m : Fin n → ℤ => ∏ i, ((1 + |(m i : ℝ)|) ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => exact Summable.of_finite
    | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).summable_iff]
      have := h1.mul_of_nonneg ih (fun _ => by positivity)
        (fun _ => Finset.prod_nonneg fun _ _ => by positivity)
      refine this.congr fun p => ?_
      simp [Fin.prod_univ_succ, Fin.consEquiv, mul_comm]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (h2 n)
  rw [Finset.prod_inv_distrib, pow_mul]
  refine inv_anti₀ (Finset.prod_pos fun _ _ => by positivity) ?_
  have h3 := Finset.prod_le_prod (s := Finset.univ) (f := fun i : Fin n => (1 + |(m i : ℝ)|) ^ 2)
    (g := fun _ => (1 + ‖(fun i => (m i : ℝ))‖) ^ 2) (fun _ _ => by positivity) (fun i _ => by
      have := norm_le_pi_norm (fun i => (m i : ℝ)) i
      rw [Real.norm_eq_abs] at this
      gcongr)
  simpa using h3
end GlobalTheory.CompanionTheory.DiracComb
