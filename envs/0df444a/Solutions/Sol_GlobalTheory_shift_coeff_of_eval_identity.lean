-- Prove2me | solution 1 for GlobalTheory.shift_coeff_of_eval_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:20.253488+00:00
-- url     : https://prove2.me/submissions/fd2d7b36-93c9-40f6-a77a-09f8532e3938

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AevalNegEqZeroOfResolventIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {N : Type} [AddCommGroup N] [Module ℂ N]
    (Ω : Module.End ℂ N) (M : ℕ) (a : ℕ → N) (ha : ∀ i, M ≤ i → a i = 0) (p : Polynomial ℂ)
    (w : N) (h : ∀ u : ℂ, u • (∑ i ∈ Finset.range M, u ^ i • a i)
      + Ω (∑ i ∈ Finset.range M, u ^ i • a i) = p.eval u • w) :
    Ω (a 0) = p.coeff 0 • w ∧ ∀ k, a k + Ω (a (k + 1)) = p.coeff (k + 1) • w := by
  have hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ),
      (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k) := by
    intro f k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · rw [ha k (by simpa using hk), map_zero]
  have key : ∀ f : N →ₗ[ℂ] ℂ,
      Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i)))
        + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i)))
        = p * Polynomial.C (f w) := by
    intro f
    apply Polynomial.funext
    intro u
    have h1 := congrArg f (h u)
    simp only [map_add, map_smul, map_sum, smul_eq_mul] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C,
      LinearMap.comp_apply]
    rw [← h1]
    simp only [mul_comm]
  refine ⟨?_, fun k => ?_⟩
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => Polynomial.coeff P 0) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C,
      zero_add] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => Polynomial.coeff P (k + 1)) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_add, map_smul, smul_eq_mul, h1, sub_self]
end GlobalTheory
