-- Prove2me | solution 1 for OAI.SnakyConditional.snaky_winning_strategy_with_legal_states
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T11:22:40.753806+00:00
-- url     : https://prove2.me/submissions/dfe524a3-32ee-4d27-98e9-b20dabb3ea8b

import Definitions.Def_SnakyConditional
import Theorems.Thm_OAI_Snaky21_empty_position_force21
import Theorems.Thm_OAI_Snaky21_force_extract

namespace OAI.Snaky21.Milestones
open OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

theorem fresh_exists (M B : Finset Cell) : ∃ m : Cell, m ∉ M ∧ m ∉ B := by
  let m : Cell := (↑(((M ∪ B).sup fun x => x.1.natAbs) + 1), 0)
  have hm : m ∉ M ∪ B := by
    intro h
    have hh := Finset.le_sup (f := fun x : Cell => x.1.natAbs) h
    simp only [m, Int.natAbs_natCast] at hh
    omega
  exact ⟨m, by simpa only [Finset.mem_union, not_or] using hm⟩

theorem won_canForce (n : ℕ) {M B : Finset Cell} (h : HasSnaky M) :
    CanForce n M B := by
  cases n with
  | zero => exact h
  | succ n =>
    obtain ⟨m, hm, hb⟩ := fresh_exists M B
    obtain ⟨r, t, ht⟩ := h
    exact ⟨m, hm, hb, Or.inl ⟨r, t, ht.trans (Finset.subset_insert _ _)⟩⟩

theorem canForce_step {n : ℕ} {M B : Finset Cell} :
    CanForce n M B → CanForce (n + 1) M B := by
  induction n generalizing M B with
  | zero => exact won_canForce 1
  | succ n ih =>
    rintro ⟨m, hm, hb, hw⟩
    refine ⟨m, hm, hb, ?_⟩
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (fun b hbm hbb => ih (hw b hbm hbb))

theorem canForce_mono {n m : ℕ} (hnm : n ≤ m) {M B : Finset Cell}
    (h : CanForce n M B) : CanForce m M B := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact canForce_step ih

theorem state_eq (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell)
    (M B : Finset Cell) (k : ℕ) :
    OAI.SnakyConditional.OrdinaryStrategy.playState σ N β M B k =
      playState σ N β M B k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [OAI.SnakyConditional.OrdinaryStrategy.playState, playState, ih]

theorem replies_eq (σ : Policy Cell) (N : ℕ) (β : ℕ → Cell) (M B : Finset Cell) :
    OAI.SnakyConditional.OrdinaryStrategy.LegalRepliesBeforeFinal σ N β M B ↔
      LegalRepliesBeforeFinal σ N β M B := by
  simp only [OAI.SnakyConditional.OrdinaryStrategy.LegalRepliesBeforeFinal,
    LegalRepliesBeforeFinal, OAI.SnakyConditional.OrdinaryStrategy.makerAt,
    makerAt, state_eq]

theorem orient_eq (r : Fin 8) (p : Cell) :
    OAI.SnakyConditional.orient r p = orient r p := by
  fin_cases r <;> rfl

theorem placement_eq (r : Fin 8) (t : Cell) :
    OAI.SnakyConditional.placement r t = placement r t := by
  funext p
  simp only [OAI.SnakyConditional.placement, placement, orient_eq]

theorem target_eq (M : Finset Cell) :
    OAI.SnakyConditional.HasSnaky M ↔ HasSnaky M := by
  simp only [OAI.SnakyConditional.HasSnaky, HasSnaky,
    OAI.SnakyConditional.snaky, snaky, placement_eq]

end OAI.Snaky21.Milestones

open OAI.SnakyConditional OAI.SnakyConditional.OrdinaryStrategy

theorem solution :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ 35 β ∅ ∅ →
        HasSnaky (playState σ 35 β ∅ ∅ 35).1 ∧
        (playState σ 35 β ∅ ∅ 35).1.card = 35 ∧
        Disjoint (playState σ 35 β ∅ ∅ 35).1 (playState σ 35 β ∅ ∅ 34).2 ∧
        ∀ k, k < 35 →
          Disjoint (playState σ 35 β ∅ ∅ k).1 (playState σ 35 β ∅ ∅ k).2 ∧
          (playState σ 35 β ∅ ∅ k).2.card = k := by
  obtain ⟨σ, hσ, hw⟩ := OAI.Snaky21.force_extract 35 (by decide)
    (OAI.Snaky21.Milestones.canForce_mono (by decide) OAI.Snaky21.empty_position_force21)
  refine ⟨σ, hσ, ?_⟩
  intro β hβ
  have h := hw β ((OAI.Snaky21.Milestones.replies_eq σ 35 β ∅ ∅).mp hβ)
  simpa only [OAI.Snaky21.Milestones.state_eq, OAI.Snaky21.Milestones.target_eq,
    Nat.reduceSub] using h
