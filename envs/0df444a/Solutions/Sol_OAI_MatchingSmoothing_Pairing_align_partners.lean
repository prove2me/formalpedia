-- Prove2me | solution 1 for OAI.MatchingSmoothing.Pairing.align_partners
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:42:48.371525+00:00
-- url     : https://prove2.me/submissions/c09fdb4c-4da9-438c-8402-b4f884a657c4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Pairings.lean:L129-L184
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.Pairing.align_partners. The node keeps its source
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

lemma align_partners [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧
      ∀ a ∈ U, (relabel p M).1 a = N.1 a := by
  classical
  let S := {a : α // a ∈ U ∧ M.1 a ∉ U}
  have hnout (a : S) : N.1 a.1 ∉ U := by
    intro hn
    have he := (hMN a.1 a.2.1 (N.1 a.1) hn).mpr rfl
    exact a.2.2 (he.symm ▸ hn)
  let f : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => M.1 a.1)
  let g : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => N.1 a.1)
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = M.1 b.1 at h
        exact False.elim (b.2.2 (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change M.1 a.1 = b.1 at h
        exact False.elim (a.2.2 (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (M.1.injective h))
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = N.1 b.1 at h
        exact False.elim (hnout b (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change N.1 a.1 = b.1 at h
        exact False.elim (hnout a (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (N.1.injective h))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hfix (a : α) (ha : a ∈ U) : p a = a := hp (Sum.inl ⟨a, ha⟩)
  have hpart (a : α) (ha : a ∈ U) : p (M.1 a) = N.1 a := by
    by_cases hm : M.1 a ∈ U
    · rw [hfix _ hm]
      exact ((hMN a ha (M.1 a) hm).mp rfl).symm
    · exact hp (Sum.inr ⟨a, ha, hm⟩)
  refine ⟨p, hfix, ?_⟩
  intro a ha
  have hi : p⁻¹ a = a := by
    calc
      p⁻¹ a = p⁻¹ (p a) := congrArg (fun b => p⁻¹ b) (hfix a ha).symm
      _ = a := by simp
  simp only [relabel_apply, hi, hpart a ha]

end Pairing
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.Pairing.align_partners := @_root_.OAI.MatchingSmoothing.Pairing.align_partners
