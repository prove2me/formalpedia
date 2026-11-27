-- Prove2me | solution 1 for GlobalTheory.span_grid_eval_eq_span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:59.266611+00:00
-- url     : https://prove2.me/submissions/60962c50-109c-4f3a-b683-6f8dc2628087

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_span_grid_eq_span_range_of_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h
end GlobalTheory
