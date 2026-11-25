-- Prove2me | solution 1 for GlobalTheory.TupleCone.coeff_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:49.528213+00:00
-- url     : https://prove2.me/submissions/5f2c89c0-ed3d-42fe-91a1-39fef98e7480

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution {p : L[X]} (hp : p ∈ cone o t) (n : ℕ) :
    p.coeff n ∈ Submodule.span o (Set.range t) ^ n := by
  induction hp using Algebra.adjoin_induction generalizing n with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      simpa using Submodule.subset_span (R := o) (Set.mem_range_self (f := t) s)
    · simp
  | algebraMap r =>
    rw [Polynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      simp
    · simp
  | add x y _ _ hx hy => rw [coeff_add]; exact add_mem (hx n) (hy n)
  | mul x y _ _ hx hy =>
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun c hc => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hc, pow_add]
    exact Submodule.mul_mem_mul (hx _) (hy _)
end GlobalTheory.TupleCone
