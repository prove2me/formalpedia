-- Prove2me | solution 1 for GlobalTheory.exists_cut_into_bounded_groups_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:03.519172+00:00
-- url     : https://prove2.me/submissions/42acf893-ee09-4bb2-afa6-9dbb7f71e112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCutIntoBoundedGroupsFinset
import Theorems.Thm_GlobalTheory_exists_le_sum_eq_of_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by
  classical
  intro s
  induction s with
  | zero =>
    intro e he
    refine ⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩
    intro k hk
    simp only [zero_mul, nonpos_iff_eq_zero] at he
    rw [Finset.sum_eq_zero_iff] at he
    simp [he k hk]
  | succ s ih =>
    intro e he
    obtain ⟨f, hfe, hfs, hfo⟩ :=
      exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)
    have hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)
    have hmul : (s + 1) * B = s * B + B := by ring
    obtain ⟨pc, hpcs, hpcb, hpco⟩ := ih (fun k => e k - f k) (by omega)
    refine ⟨Fin.cons f pc, ?_, ?_, ?_⟩
    · intro k hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hpcs k hk]
      exact Nat.add_sub_cancel' (hfe k)
    · intro u
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        omega
      · simp only [Fin.cons_succ]
        exact hpcb i
    · intro u k hk
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        exact hfo k hk
      · simp only [Fin.cons_succ]
        exact hpco i k hk
end GlobalTheory
