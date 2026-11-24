-- Prove2me | solution 1 for GlobalTheory.span_grid_eq_span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:42.744365+00:00
-- url     : https://prove2.me/submissions/fc5c5226-a98e-4b3c-a01f-0a59fd98ff96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_mem_of_grid_mem

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
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩
end GlobalTheory
