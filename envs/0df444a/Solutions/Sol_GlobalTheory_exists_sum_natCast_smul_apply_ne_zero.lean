-- Prove2me | solution 1 for GlobalTheory.exists_sum_natCast_smul_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:46.477397+00:00
-- url     : https://prove2.me/submissions/3c2d7f00-030f-4f91-bdbc-d063c5e78906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_exists_sum_nsmul_apply_ne_zero

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
variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]
variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]
namespace GlobalTheory
theorem _root_.solution [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by
  have : ∀ j, IsAddTorsionFree (W j) := fun j => IsAddTorsionFree.of_isTorsionFree K (W j)
  simp only [Nat.cast_smul_eq_nsmul]
  exact exists_sum_nsmul_apply_ne_zero (fun j => (l j).toAddMonoidHom) s h
end GlobalTheory
