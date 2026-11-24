-- Prove2me | solution 1 for GlobalTheory.antitone_filtration_exists_adapted_linearIndep_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:20.490326+00:00
-- url     : https://prove2.me/submissions/8bcfada8-b9c8-4233-9d45-0f8397e3264d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AntitoneFiltrationExistsAdaptedLinearIndepSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Submodule
namespace GlobalTheory
theorem _root_.solution {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩
    simp only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]
    rw [eq_bot_iff, ← hhi]
    exact hA (by simpa using ha)
  | succ n ih =>
    obtain ⟨s, k, hs, hk, hspan⟩ := ih
    have hsA : s ⊆ A (hi - (n + 1 : ℕ)) := by
      intro x hx
      have hx' : x ∈ A (hi - n) := by
        rw [hspan _ le_rfl]
        exact Submodule.subset_span ⟨hx, hk x hx⟩
      exact hA (by push_cast; omega) hx'
    obtain ⟨t, htA, hst, hAt, ht⟩ := exists_linearIndepOn_id_extension hs hsA
    have hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ)) := by
      intro x _
      split_ifs with h
      · have := hk x h
        push_cast at this ⊢
        omega
      · exact le_rfl
    refine ⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤
          (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩
      rw [hset]
      exact le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)
    · have ha' : hi - (n : ℤ) ≤ a := by
        push_cast at h
        omega
      rw [hspan a ha']
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hkx⟩
        exact ⟨hst hx, by rw [if_pos hx]; exact hkx⟩
      · rintro ⟨hx, hkx⟩
        split_ifs at hkx with hxs
        · exact ⟨hxs, hkx⟩
        · push_cast at h hkx
          omega
end GlobalTheory
