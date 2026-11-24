-- Prove2me | solution 1 for GlobalTheory.CoeffWord.eq_of_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:38.966979+00:00
-- url     : https://prove2.me/submissions/cb4142d5-65d6-466a-a08e-f471212c019f

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hs : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s))
    (h : ∀ v : Fin r × Fin n, v.2.val < v.1.val → m v = e v) : m = e := by
  have key : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [hm a s h1, he a s h1]
    · exact h (a, s) h1
  ext ⟨a, s⟩
  by_cases ha : a.val = s.val
  · have h1 := hs s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      Finset.sum_congr rfl (fun b hb => key b s (fun hb' =>
        (Finset.ne_of_mem_erase hb) (Fin.ext (hb'.trans ha.symm))))] at h1
    exact Nat.add_right_cancel h1
  · exact key a s ha
end GlobalTheory.CoeffWord
