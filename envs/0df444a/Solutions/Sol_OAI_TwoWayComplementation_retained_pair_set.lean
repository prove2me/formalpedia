-- Prove2me | solution 1 for OAI.TwoWayComplementation.retained_pair_set
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:05:31.218722+00:00
-- url     : https://prove2.me/submissions/4bbe1de3-1841-4218-9e5f-cddcb7ff3f4d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean:L39-L76
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.retained_pair_set. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

-- ---- from OAI.Combinatorics.TwoWayAutomata.Retained ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Retaining a new pair and all external points removes exactly 127 points. -/
theorem retained_pair_set {H : Type*} [Finite H] (U V : Set H)
    (hU : U.ncard = 64) (hV : V.ncard = 64) (hUV : Disjoint U V)
    (z x y : H) (hzU : z ∉ U) (hzV : z ∉ V) (hx : x ∈ U) (hy : y ∈ V) :
    ∃ F : Set H, Nat.card F = Nat.card H - 127 ∧ x ∈ F ∧ y ∈ F ∧ z ∉ F ∧
      (∀ a ∈ U, a ∈ F → a = x) ∧ (∀ b ∈ V, b ∈ F → b = y) := by
  classical
  let S := insert z (U ∪ V)
  let F := ({x, y} : Set H) ∪ Sᶜ
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hUV (h ▸ hx) hy
  have hS : S.ncard = 129 := by
    rw [Set.ncard_insert_of_notMem (by simpa using And.intro hzU hzV),
      Set.ncard_union_eq hUV, hU, hV]
  have hpair : ({x, y} : Set H).ncard = 2 := by simp [hxy]
  have hpS : ({x, y} : Set H) ⊆ S := by
    rintro a (rfl | rfl) <;> simp [S, hx, hy]
  have hdisj : Disjoint ({x, y} : Set H) Sᶜ := Set.disjoint_left.mpr (fun _ ha hn => hn (hpS ha))
  have hF : F.ncard = Nat.card H - 127 := by
    rw [Set.ncard_union_eq hdisj, hpair, Set.ncard_compl, hS]
    have hh : 129 ≤ Nat.card H := by simpa only [hS] using Set.ncard_le_card S
    omega
  refine ⟨F, by simpa only [Nat.card_coe_set_eq] using hF, Or.inl (Or.inl rfl),
    Or.inl (Or.inr rfl), ?_, ?_, ?_⟩
  · rintro (h | h)
    · rcases h with rfl | rfl
      · exact hzU hx
      · exact hzV hy
    · exact h (by simp [S])
  · intro a ha hF
    rcases hF with (rfl | rfl) | hout
    · rfl
    · exact (Set.disjoint_left.mp hUV ha hy).elim
    · exact (hout (by simp [S, ha])).elim
  · intro b hb hF
    rcases hF with (rfl | rfl) | hout
    · exact (Set.disjoint_left.mp hUV hx hb).elim
    · rfl
    · exact (hout (by simp [S, hb])).elim

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.retained_pair_set := @_root_.OAI.TwoWayComplementation.retained_pair_set
