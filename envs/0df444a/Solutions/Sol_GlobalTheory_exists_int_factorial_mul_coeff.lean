-- Prove2me | solution 1 for GlobalTheory.exists_int_factorial_mul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:27.510636+00:00
-- url     : https://prove2.me/submissions/c9e0e258-568e-4674-9a69-92853febd94c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {e : ℕ} {P : ℚ[X]} (he : P.degree ≤ e)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, P.eval (n : ℚ) = z) :
    ∃ z : ℤ, (e.factorial : ℚ) * P.coeff e = z := by
  induction e generalizing P with
  | zero =>
    obtain ⟨n, z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    rw [eq_C_of_degree_le_zero he] at hz
    simpa using hz
  | succ e ih =>
    have h1 := degree_comp_X_add_C_sub_lt P 1 (e + 1) he
    obtain ⟨z, hz⟩ := ih (P := P.comp (X + C 1) - P)
      (degree_le_iff_coeff_zero _ _ |>.2 fun m hm => (degree_lt_iff_coeff_zero _ _).1 h1 m
        (by exact_mod_cast hm)) (by
        filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h] with n ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨b - a, ?_⟩
        simp only [eval_sub, eval_comp, eval_add, eval_X, eval_C]
        push_cast at hb ⊢
        rw [ha, hb])
    refine ⟨z, ?_⟩
    rw [← hz, coeff_comp_X_add_C_sub P 1 e he, Nat.factorial_succ]
    push_cast
    ring
end GlobalTheory
