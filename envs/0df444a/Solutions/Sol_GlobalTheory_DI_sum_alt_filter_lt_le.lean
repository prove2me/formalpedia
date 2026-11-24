-- Prove2me | solution 1 for GlobalTheory.DI.sum_alt_filter_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:41.078004+00:00
-- url     : https://prove2.me/submissions/5a52f94f-bb09-4879-91eb-0b3326880cde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechDeltaCupProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
namespace GlobalTheory.DI
theorem _root_.solution (F : Finset ι → E) (u : Finset ι) :
    ∑ j ∈ u, (-1 : ℤ) ^ (u.filter (· < j)).card • (F (u.filter (· < j)) + F (u.filter (· ≤ j))) =
      F ∅ - (-1 : ℤ) ^ u.card • F u := by
  induction u using Finset.induction_on_max with
  | empty => simp
  | insert m u hm ih =>
    have hmu : m ∉ u := fun h => lt_irrefl m (hm m h)
    rw [Finset.sum_insert hmu]
    rw [Finset.sum_congr rfl (g := fun j => (-1 : ℤ) ^ (u.filter (· < j)).card •
        (F (u.filter (· < j)) + F (u.filter (· ≤ j)))) (fun j hj => by
      rw [Finset.filter_insert, if_neg (not_lt.2 (hm j hj).le), Finset.filter_insert,
        if_neg (not_le.2 (hm j hj))]), ih]
    have e1 : (insert m u).filter (· < m) = u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxm⟩
        · exact absurd hxm (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hm x hx⟩
    have e2 : (insert m u).filter (· ≤ m) = insert m u := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · exact fun h => h.1
      · rintro (rfl | hx)
        · exact ⟨Or.inl rfl, le_rfl⟩
        · exact ⟨Or.inr hx, (hm x hx).le⟩
    rw [e1, e2, Finset.card_insert_of_notMem hmu, pow_succ, smul_add, mul_neg_one, neg_smul]
    abel
end GlobalTheory.DI
