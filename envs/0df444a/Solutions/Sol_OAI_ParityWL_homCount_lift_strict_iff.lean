-- Prove2me | solution 1 for OAI.ParityWL.homCount_lift_strict_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:06:28.723378+00:00
-- url     : https://prove2.me/submissions/049016aa-8e8e-4e76-a8b7-f8dc39304160

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean:L161-L176
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.homCount_lift_strict_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

-- ---- from OAI.Combinatorics.ParityLifts.LiftCounts ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype V] in
lemma solutions_card_eq_of_nonempty (b : A → Bit)
    (h : Nonempty (Solutions T G F τ φ b)) :
    Fintype.card (Solutions T G F τ φ b) =
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  obtain ⟨v⟩ := h
  exact Fintype.card_congr (homogeneousTranslate T G F τ φ b v)

omit [Fintype V] in
lemma solutions_card_le (b : A → Bit) :
    Fintype.card (Solutions T G F τ φ b) ≤
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  classical
  by_cases h : Nonempty (Solutions T G F τ φ b)
  · exact (solutions_card_eq_of_nonempty T G F τ φ b h).le
  · have : IsEmpty (Solutions T G F τ φ b) := not_nonempty_iff.mp h
    simp

omit [Fintype V] in
lemma solutions_card_eq_iff (b : A → Bit) :
    Fintype.card (Solutions T G F τ φ b) =
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) ↔
      Nonempty (Solutions T G F τ φ b) := by
  constructor
  · intro h
    have : Nonempty (Solutions T G F τ φ (fun _ => 0)) :=
      ⟨zeroSolution T G F τ φ⟩
    apply Fintype.card_pos_iff.mp
    rw [h]
    exact Fintype.card_pos
  · exact solutions_card_eq_of_nonempty T G F τ φ b

lemma homCount_lift (b : A → Bit) :
    homCount F (liftGraph T G τ b) =
      ∑ φ : F →g G, Fintype.card (Solutions T G F τ φ b) := by
  classical
  unfold homCount
  rw [Fintype.card_congr (homSolutionsEquiv T G F τ b), Fintype.card_sigma]

/-- Noncancellation for every uncolored homomorphism, not just typed witnesses. -/
theorem homCount_lift_le (b : A → Bit) :
    homCount F (liftGraph T G τ b) ≤ homCount F (liftGraph T G τ (fun _ => 0)) := by
  classical
  rw [homCount_lift T G F τ b, homCount_lift T G F τ (fun _ => 0)]
  exact Finset.sum_le_sum (fun φ _ => solutions_card_le T G F τ φ b)

lemma homCount_lift_eq_iff (b : A → Bit) :
    homCount F (liftGraph T G τ b) = homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∀ φ : F →g G, Nonempty (Solutions T G F τ φ b) := by
  classical
  rw [homCount_lift T G F τ b, homCount_lift T G F τ (fun _ => 0),
    Finset.sum_eq_sum_iff_of_le (fun φ _ => solutions_card_le T G F τ φ b)]
  simp only [Finset.mem_univ, forall_const, solutions_card_eq_iff]

/-- A strict uncolored count gap comes from an inconsistent projected system. -/
theorem homCount_lift_strict_iff (b : A → Bit) :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, ¬ Nonempty (Solutions T G F τ φ b) := by
  have hle := homCount_lift_le T G F τ b
  have heq := homCount_lift_eq_iff T G F τ b
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have := heq.mpr hn
    omega
  · rintro ⟨φ, hφ⟩
    have hn : homCount F (liftGraph T G τ b) ≠
        homCount F (liftGraph T G τ (fun _ => 0)) := fun h => hφ (heq.mp h φ)
    omega

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

end BinaryDuality

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.homCount_lift_strict_iff := @_root_.OAI.ParityWL.homCount_lift_strict_iff
