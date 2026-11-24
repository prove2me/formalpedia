-- Prove2me | solution 1 for GlobalTheory.Wick.factorial_smul_dividedContraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:54.722944+00:00
-- url     : https://prove2.me/submissions/150ead3d-c860-4dd3-9cb3-cece15970d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_induction_inl
import Theorems.Thm_GlobalTheory_Wick_contraction_rename_inr
import Theorems.Thm_GlobalTheory_Wick_contraction_pow_X_inl_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]
namespace GlobalTheory.Wick
theorem _root_.solution (γ : ι → κ → R) (n : ℕ) :
    n.factorial • dividedContraction γ n = contraction γ ^ n := by
  refine LinearMap.ext fun P => ?_
  rw [LinearMap.smul_apply]
  induction P using induction_inl generalizing n with
  | h0 q =>
    rcases n with _ | n
    · simp
    · rw [dividedContraction_succ_rename_inr, pow_succ, Module.End.mul_apply,
        contraction_rename_inr, map_zero, smul_zero]
  | hadd P Q hP hQ => rw [map_add, map_add, smul_add, hP, hQ]
  | h P i hP =>
    rcases n with _ | n
    · simp
    · rw [dividedContraction_succ_X_inl_mul, contraction_pow_X_inl_mul, smul_add, ← mul_smul_comm,
        hP, ← hP n, map_nsmul, smul_smul, Nat.factorial_succ]
end GlobalTheory.Wick
