-- Prove2me | solution 1 for GlobalTheory.exists_poly_dual_sum_monomial_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:53.027889+00:00
-- url     : https://prove2.me/submissions/a75bf273-be5d-42cc-bb8b-33fd1258e261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe

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
omit [Finite σ] [CharZero K]
namespace GlobalTheory
theorem _root_.solution (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i
  · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]
end GlobalTheory
