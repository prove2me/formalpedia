-- Prove2me | solution 1 for LatinQuarter.Textbook.exists_criticalSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:07.278988+00:00
-- url     : https://prove2.me/submissions/4897b5b2-f7af-4e50-bb1a-beb29b457eb3

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution {n : ℕ} {L : Fin n → Fin n → Fin n} :
    ∀ (k : ℕ) (T : Finset (Fin n × Fin n × Fin n)), T.card = k →
      DefiningSet L T → ∃ T' ⊆ T, CriticalSet L T' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro T hk hT
    by_cases hc : ∀ t ∈ T, 1 < numCompletions (T.erase t)
    · exact ⟨T, subset_refl T, hT, hc⟩
    push Not at hc
    obtain ⟨t, ht, hle⟩ := hc
    have hLc : Completes (T.erase t) L :=
      ⟨hT.1.1, fun u hu => hT.1.2 u (Finset.mem_of_mem_erase hu)⟩
    rw [numCompletions] at hle
    have hsub := (Finite.card_le_one_iff_subsingleton).mp hle
    have hdef : DefiningSet L (T.erase t) :=
      ⟨hLc, fun M hM => congrArg Subtype.val
        (Subsingleton.elim (⟨M, hM⟩ : {M // Completes (T.erase t) M}) ⟨L, hLc⟩)⟩
    obtain ⟨T', hsub', hcrit⟩ := ih (T.erase t).card
      (hk ▸ Finset.card_erase_lt_of_mem ht) (T.erase t) rfl hdef
    exact ⟨T', hsub'.trans (Finset.erase_subset t T), hcrit⟩
end LatinQuarter.Textbook
