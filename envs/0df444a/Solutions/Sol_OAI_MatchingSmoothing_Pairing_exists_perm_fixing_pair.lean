-- Prove2me | solution 1 for OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:44:15.258404+00:00
-- url     : https://prove2.me/submissions/180965a6-6c1b-4f27-8a96-c240fe8e4925

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Pairings.lean:L379-L396
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma exists_perm_fixing_pair [Fintype α] [DecidableEq α]
    (U : Finset α) {a b c d : α} (ha : a ∉ U) (hb : b ∉ U)
    (hc : c ∉ U) (hd : d ∉ U) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : Equiv.Perm α, (∀ u ∈ U, p u = u) ∧ p a = c ∧ p b = d := by
  let f : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i b a)
  let g : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i d c)
  have hi {x y : α} (hx : x ∉ U) (hy : y ∉ U) (hxy : x ≠ y) :
      Function.Injective (Sum.elim (Subtype.val : U → α) (fun i : Bool => cond i y x)) := by
    rw [Sum.elim_injective]
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro i j h
      cases i <;> cases j <;> simp_all
    · intro u i
      cases i <;> simp only [Bool.cond_false, Bool.cond_true]
      · intro h; exact hx (h ▸ u.2)
      · intro h; exact hy (h ▸ u.2)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g (hi ha hb hab) (hi hc hd hcd)
  exact ⟨p, fun u hu => hp (Sum.inl ⟨u, hu⟩), hp (Sum.inr false), hp (Sum.inr true)⟩

end Pairing
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair := @_root_.OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair
