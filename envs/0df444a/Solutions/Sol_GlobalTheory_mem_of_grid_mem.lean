-- Prove2me | solution 1 for GlobalTheory.mem_of_grid_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:26.09248+00:00
-- url     : https://prove2.me/submissions/bd43bea1-0e6b-4daa-aedc-ef9748eec064

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_eq_zero_of_eval_grid_eq_zero

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
theorem _root_.solution (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]
end GlobalTheory
