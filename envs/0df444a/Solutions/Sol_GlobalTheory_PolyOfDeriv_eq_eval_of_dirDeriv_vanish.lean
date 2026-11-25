-- Prove2me | solution 1 for GlobalTheory.PolyOfDeriv.eq_eval_of_dirDeriv_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:05.1924+00:00
-- url     : https://prove2.me/submissions/a69d5039-fe27-47c6-b8d6-ca0ac137a264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish
import Theorems.Thm_GlobalTheory_PolyOfDeriv_taylor_of_chain
import Theorems.Thm_GlobalTheory_PolyOfDeriv_hasDerivAt_iter
import Theorems.Thm_GlobalTheory_PolyOfDeriv_foldr_replicate
import Theorems.Thm_GlobalTheory_PolyOfDeriv_multilinear_diag_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.PolyOfDeriv
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp
end GlobalTheory.PolyOfDeriv
