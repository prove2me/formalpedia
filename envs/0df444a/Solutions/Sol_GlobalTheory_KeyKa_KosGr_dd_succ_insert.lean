-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.dd_succ_insert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:07.562866+00:00
-- url     : https://prove2.me/submissions/505c1942-ca20-4152-b45c-fd27055da117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (t : Fin g)
    (c : Finset (Fin g) → ∀ j, V j) (I : Finset (Fin g)) (j : ℕ) :
    dd x (t.val + 1) c (insert t I) j = dd x t.val (fun J => c (insert t J)) I j := by
  unfold dd
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hit : i.val < t.val
  · have hne : i ≠ t := fun h => by rw [h] at hit; exact lt_irrefl _ hit
    have hf : (insert t I).filter (· < i) = I.filter (· < i) := by
      rw [Finset.filter_insert, if_neg (fun h : t < i => absurd (lt_trans hit h) (lt_irrefl _))]
    have hmem : i ∉ insert t I ↔ i ∉ I := by simp [hne]
    rw [hf, Finset.insert_comm i t]
    simp only [hmem, Nat.lt_succ_of_lt hit, hit, true_and]
  · have h1 : ¬ (i.val < t.val + 1 ∧ i ∉ insert t I) := by
      rintro ⟨h, hi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact hit h
      · exact hi (Finset.mem_insert.mpr (Or.inl (Fin.ext h)))
    rw [if_neg h1, if_neg (fun h => hit h.1)]
end GlobalTheory.KeyKa.KosGr
