-- Prove2me | solution 1 for GlobalTheory.MinorNorm.partition_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:36.378035+00:00
-- url     : https://prove2.me/submissions/2065fbe0-d133-44b5-a157-0d40a83b2c27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (p : (Fin l → ℕ) → Prop) (h0 : p 0)
    (hs : ∀ (a : Fin l → ℕ) (K : Fin l), Antitone a → (∀ i, K < i → a i = 0) → p a →
      p (addCol a K)) (a : Fin l → ℕ) (ha : Antitone a) : p a := by
  induction hN : ∑ i, a i using Nat.strong_induction_on generalizing a with
  | _ N ih =>
  by_cases h : a = 0
  · exact h ▸ h0
  · have hne : (Finset.univ.filter fun i => a i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, by simpa using hi⟩
    set K := (Finset.univ.filter fun i => a i ≠ 0).max' hne with hK
    have hK1 : a K ≠ 0 := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hK2 : ∀ i, K < i → a i = 0 := by
      intro i hi
      by_contra h'
      exact absurd (Finset.le_max' _ i (by simpa using h')) (not_le.mpr hi)
    have hK3 : ∀ i, i ≤ K → 1 ≤ a i := fun i hi => (Nat.one_le_iff_ne_zero.mpr hK1).trans (ha hi)
    have e : addCol (fun i => a i - 1) K = a := by
      ext i
      simp only [addCol]
      split_ifs with hi
      · have := hK3 i hi
        omega
      · rw [hK2 i (not_le.mp hi)]
    have ha' : Antitone fun i => a i - 1 := fun i j hij => Nat.sub_le_sub_right (ha hij) 1
    rw [← e]
    refine hs _ K ha' (fun i hi => by simp [hK2 i hi]) (ih _ ?_ _ ha' rfl)
    rw [← hN]
    refine Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _) ⟨K, Finset.mem_univ _, ?_⟩
    have := hK3 K le_rfl
    omega
end GlobalTheory.MinorNorm
