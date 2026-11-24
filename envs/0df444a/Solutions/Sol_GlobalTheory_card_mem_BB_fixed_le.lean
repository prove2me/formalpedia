-- Prove2me | solution 1 for GlobalTheory.card_mem_BB_fixed_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:27.988363+00:00
-- url     : https://prove2.me/submissions/9b7f55ac-cbab-40bf-806e-1dfb8b13ca65

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Theorems.Thm_GlobalTheory_card_exc_fixed_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (hR : Formalism.CyclotomicNorms.RootsOfUnityCount) (Y : ℝ) (hY : 2 ≤ Y) (ℓ N : ℕ)
    (T : Finset ℕ) (hT : ∀ g ∈ T, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ ℓ ∈ Formalism.CyclotomicNorms.BB N g) :
    (T.card : ℝ) ≤ 1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  have hY0 : 0 ≤ Y ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hsub : T ⊆ T.filter (fun g => g = ℓ) ∪
      (Finset.Icc 1 N).biUnion (fun d => T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)) := by
    intro g hg
    have h := (hT g hg).2.2
    simp only [Formalism.CyclotomicNorms.BB, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at h
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    rcases h with h | ⟨d, hd1, hdN, hex⟩
    · exact Or.inl ⟨hg, h.symm⟩
    · exact Or.inr ⟨d, Finset.mem_Icc.2 ⟨hd1, hdN⟩, Finset.mem_filter.2 ⟨hg, hex⟩⟩
  have h0 : (T.filter (fun g => g = ℓ)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    rw [(Finset.mem_filter.1 ha).2, (Finset.mem_filter.1 hb).2]
  have hd : ∀ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      2 * N * (Y ^ ((3 : ℝ) / 4) + 1) := by
    intro d hdm
    obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hdm
    have h1 := card_exc_fixed_le hR Y hY ℓ d hd1 (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ))
      (fun g hg => ⟨(hT g (Finset.mem_filter.1 hg).1).1, (hT g (Finset.mem_filter.1 hg).1).2.1,
        (Finset.mem_filter.1 hg).2⟩)
    have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
    have h2 := mul_le_mul_of_nonneg_right hdN' (by linarith : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1)
    linarith
  have hc1 : T.card ≤ (T.filter (fun g => g = ℓ)).card +
      ∑ d ∈ Finset.Icc 1 N, (T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hc2 : (T.card : ℝ) ≤
      1 + ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) := by
    have h1 := (Nat.cast_le (α := ℝ)).2 hc1
    push_cast at h1
    have h0' : ((T.filter (fun g => g = ℓ)).card : ℝ) ≤ 1 := by exact_mod_cast h0
    linarith
  have hc3 : ∑ d ∈ Finset.Icc 1 N, ((T.filter (fun g => Formalism.CyclotomicNorms.Exc g d ℓ)).card : ℝ) ≤
      N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hd
      _ = N * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have e : (N : ℝ) * (2 * N * (Y ^ ((3 : ℝ) / 4) + 1)) = 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1) := by
    ring
  linarith
end GlobalTheory
