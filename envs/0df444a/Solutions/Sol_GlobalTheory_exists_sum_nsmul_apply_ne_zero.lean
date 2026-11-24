-- Prove2me | solution 1 for GlobalTheory.exists_sum_nsmul_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:07.277216+00:00
-- url     : https://prove2.me/submissions/fb9a917e-c71c-46c0-8f30-90804f8f6d4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_exists_sum_nsmul_apply_ne_zero_finset

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
namespace GlobalTheory
theorem _root_.solution [∀ j, IsAddTorsionFree (W j)] [Fintype κ]
    (l : ∀ j, V →+ W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, c k • s k) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := exists_sum_nsmul_apply_ne_zero_finset l s Finset.univ
  exact ⟨c, hc, fun j => hl j ((h j).imp fun k hk => ⟨Finset.mem_univ k, hk⟩)⟩
end GlobalTheory
